--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  The compiler's state and its code generator, a port of PUC Lua's lcode.c. Only the
--  compiler uses it.

with Interfaces;
with Pyro.Diagnostics;     use Pyro.Diagnostics;
with Pyro.Floats;
with Pyro.Growable_Arrays;
with Pyro.Tokens;

package Pyro.Compiler.Code with SPARK_Mode => On, Always_Terminates is

   --  A position in one of the compiler's arrays.
   type Work_Position is range 1 .. 2 ** 28;

   --  A count of entries or a position in the compiler's arrays, as a number: bounded, so sums
   --  of two do not overflow.
   subtype Bounded_Count is Natural range 0 .. 2 ** 28;

   --  [puc lcode.h:NO_JUMP] The end of a jump list, and a jump list: the program counter of
   --  its first jump.
   No_Jump : constant := -1;
   subtype Jump_List is Integer range No_Jump .. Entry_Number'Last;

   --  [puc lopcodes.h:NO_REG] No register, in the A operand of a TESTSET to be patched.
   No_Register : constant := 255;

   --  [puc lparser.h:expkind] What an expression descriptor holds.
   type Expression_Kind is
     (Void,                   --  VVOID: no value (an empty list, or a global's _ENV not found)
      Nil_Value,              --  VNIL
      True_Value,             --  VTRUE
      False_Value,            --  VFALSE
      Constant_Index,         --  VK: constant Info
      Float_Value,            --  VKFLT: Float_Bits
      Integer_Value,          --  VKINT: Integer_Bits
      String_Value,           --  VKSTR: String_Symbol
      Fixed_Register,         --  VNONRELOC: register Info
      Local_Register,         --  VLOCAL: register Register of variable Variable
      Upvalue_Slot,           --  VUPVAL: upvalue Info
      Compile_Time_Constant,  --  VCONST: variable Info (absolute) holds the value
      Indexed_Register,       --  VINDEXED: register Table indexed by register Key
      Indexed_Upvalue,        --  VINDEXUP: upvalue Table indexed by constant Key
      Indexed_Integer,        --  VINDEXI: register Table indexed by the integer Key
      Indexed_String,         --  VINDEXSTR: register Table indexed by constant Key
      Comparison,             --  VJMP: the test before the jump at Info
      Relocatable,            --  VRELOC: instruction Info puts the value in its A register
      Open_Call,              --  VCALL: the call at Info
      Open_Vararg);           --  VVARARG: the VARARG at Info

   --  [puc lparser.h:expdesc] An expression being compiled.
   type Expression is record
      Kind          : Expression_Kind := Void;
      Info          : Natural := 0;
      Integer_Bits  : Interfaces.Integer_64 := 0;
      Float_Bits    : Floats.Float_Bits := 0;
      String_Symbol : Symbol_Index := No_Symbol;
      String_Short  : Boolean := True;
      Table         : Natural := 0;
      Key           : Natural := 0;
      Register      : Natural := 0;
      Variable      : Natural := 0;
      True_List     : Jump_List := No_Jump;
      False_List    : Jump_List := No_Jump;
   end record;

   --  [puc lparser.h] The kind of a local variable: regular, <const>, <close>, or a <const>
   --  whose value is known at compile time (it has no register).
   type Variable_Kind is
     (Regular_Variable, Constant_Variable, Close_Variable, Compile_Time_Variable);

   --  [puc lparser.h:Vardesc] A declared local variable.
   type Variable_Entry is record
      Name        : Symbol_Index := No_Symbol;
      Kind        : Variable_Kind := Regular_Variable;
      Register    : Bounded_Count := 0;
      Debug_Index : Bounded_Count := 0;
      Value       : Constant_Value := (others => <>);
   end record;

   --  [puc lobject.h:Upvaldesc] An upvalue of an open function, with its variable's kind.
   type Upvalue_Entry is record
      Name     : Symbol_Index := No_Symbol;
      In_Stack : Boolean := False;
      Index    : Bounded_Count := 0;
      Kind     : Variable_Kind := Regular_Variable;
   end record;

   --  [puc lparser.h:Labeldesc] A visible label or a pending goto.
   type Label_Entry is record
      Name   : Symbol_Index := No_Symbol;
      Line   : Line_Number := 1;
      Active : Bounded_Count := 0;
      Close  : Boolean := False;
      PC     : Jump_List := 0;
   end record;

   --  [puc lparser.c:BlockCnt] An open block.
   type Block_Entry is record
      Active              : Bounded_Count := 0;
      First_Label         : Bounded_Count := 0;
      First_Goto          : Bounded_Count := 0;
      Has_Upvalue         : Boolean := False;
      Is_Loop             : Boolean := False;
      Inside_To_Be_Closed : Boolean := False;
   end record;

   --  [puc lparser.h:FuncState] An open function. Its instructions, constants, local variable
   --  records and children are the entries after the Bases in the shared arrays (an inner
   --  function's are after its parent's, and move to the chunk when it closes); its upvalues
   --  are a fixed block of slots for its depth.
   type Function_Entry is record
      Code_Base     : Bounded_Count := 0;
      Constant_Base : Bounded_Count := 0;
      Debug_Base    : Bounded_Count := 0;
      Child_Base    : Bounded_Count := 0;
      Upvalue_Count : Bounded_Count := 0;
      First_Local   : Bounded_Count := 0;
      First_Label   : Bounded_Count := 0;
      Active        : Bounded_Count := 0;
      Free_Register : Bounded_Count := 0;
      Last_Target   : Bounded_Count := 0;
      Block_Base    : Bounded_Count := 0;
      Needs_Close   : Boolean := False;
      Facts         : Prototype_Header := (others => <>);
   end record;

   --  [puc lcode.c:addk] What the scanner table of PUC Lua maps to a constant index: Lua table
   --  keys (an integral float is an integer key).
   type Key_Kind is (Nil_Key, False_Key, True_Key, Integer_Key, Float_Key, String_Key);

   type Cache_Entry is record
      Used   : Boolean := False;
      Kind   : Key_Kind := Nil_Key;
      Bits   : Interfaces.Unsigned_64 := 0;
      Symbol : Symbol_Index := No_Symbol;
      Index  : Natural := 0;
   end record;

   --  A token of the chunk: its kind, its last byte and PUC Lua's line once it is read.
   type Token_Entry is record
      Kind : Tokens.Token_Kind := Tokens.End_Of_Stream;
      Last : Span_End := 0;
      Line : Line_Number := 1;
   end record;

   --  [puc lparser.c:MAXUPVAL] The most upvalues of a function; each open function has this
   --  many upvalue slots.
   Maximum_Upvalues : constant := 255;

   --  [puc lparser.c:MAXVARS] The most local variables active in a function.
   Maximum_Variables : constant := 200;

   --  [puc lopcodes.h:LFIELDS_PER_FLUSH] List items stored by one SETLIST.
   Fields_Per_Flush : constant := 50;

   --  [puc lua.h:LUA_MULTRET] All results.
   Multiple_Results : constant := -1;

   --  Everything the compiler works on: the open functions, their code, constants, variables,
   --  blocks, labels and gotos, and the chunk's tokens. It owns heap memory: release it with
   --  Release.
   type Compiler_State is limited private
   with
     Default_Initial_Condition =>
       Is_Released (Compiler_State) and then not Failed (Compiler_State),
     Annotate => (GNATprove, Ownership, "Needs_Reclamation");

   --  True when the state holds no heap memory.
   function Is_Released (State : Compiler_State) return Boolean
   with Global => null, Annotate => (GNATprove, Ownership, "Is_Reclaimed");

   --  The compilation has stopped (an error, or an internal error).
   function Failed (State : Compiler_State) return Boolean
   with Global => null;

   --  The compilation stopped at a compile-time limit (rather than an internal error), and
   --  that error.
   function Has_Error (State : Compiler_State) return Boolean
   with Global => null;

   function Error_Of (State : Compiler_State) return Diagnostic
   with Global => null;

   --  Makes the stop an internal error (the chunk failed its validity check).
   procedure Make_Internal_Error (State : in out Compiler_State)
   with Global => null, Post => Failed (State) and then not Has_Error (State);

   --  The memory budget the compiler charges.
   function Budget_Of (State : Compiler_State) return Memory_Budget
   with Global => null;

   procedure Set_Budget (State : in out Compiler_State; Budget : Memory_Budget)
   with Global => null, Post => Budget_Of (State) = Budget;

   --  The names the compiler makes up: "_ENV", "break", "self" and "(for state)".
   function Environment_Name (State : Compiler_State) return Symbol_Index
   with Global => null;
   function Break_Name (State : Compiler_State) return Symbol_Index
   with Global => null;
   function Self_Name (State : Compiler_State) return Symbol_Index
   with Global => null;
   function For_State_Name (State : Compiler_State) return Symbol_Index
   with Global => null;

   procedure Set_Names
     (State : in out Compiler_State; Environment, Break, Self, For_State : Symbol_Index)
   with Global => null;

   --  Reads the chunk's tokens again, for their lines; an internal error if they do not read
   --  as before.
   procedure Read_Tokens
     (State : in out Compiler_State; Source : Sources.Source; Symbols : in out Symbol_Table)
   with Global => null, Pre => Is_Valid (Symbols), Post => Is_Valid (Symbols);

   --  The kind of token Ordinal (End_Of_Stream if there is none).
   function Token_Kind_At (State : Compiler_State; Ordinal : Natural) return Tokens.Token_Kind
   with Global => null;

   --  [puc llex.c:luaX_next] Token Ordinal has been read: it is the token read last.
   procedure Consume (State : in out Compiler_State; Ordinal : Natural)
   with Global => null;

   --  Token Ordinal, a name, is read after PUC Lua looked past it (a field of a table
   --  constructor), so reading it leaves lastline at the next token's line; 0 for none.
   procedure Set_Lookahead_Name (State : in out Compiler_State; Ordinal : Natural)
   with Global => null;

   --  The stack of nodes of the chains of operators and suffixes being walked.
   function Spine_Length (State : Compiler_State) return Natural
   with Global => null, Post => Spine_Length'Result <= 2 ** 28;

   function Spine_Node (State : Compiler_State; Position : Positive) return Node_Index
   with Global => null;

   procedure Push_Node (State : in out Compiler_State; Node : Node_Index; Success : out Boolean)
   with Global => null;

   procedure Truncate_Spine (State : in out Compiler_State; Length : Natural)
   with Global => null;

   --  The stack of the targets of the assignments being compiled.
   function Targets_Length (State : Compiler_State) return Natural
   with Global => null, Post => Targets_Length'Result <= 2 ** 28;

   function Target_At (State : Compiler_State; Position : Positive) return Expression
   with Global => null;

   procedure Set_Target (State : in out Compiler_State; Position : Positive; Item : Expression)
   with Global => null;

   procedure Push_Target (State : in out Compiler_State; Item : Expression; Success : out Boolean)
   with Global => null;

   procedure Truncate_Targets (State : in out Compiler_State; Length : Natural)
   with Global => null;

   --  The number of prototypes nested in the open function so far.
   function Child_Count (State : Compiler_State) return Natural
   with Global => null;

   --  [puc lparser.c:mainfunc] Gives the open (main) function its _ENV upvalue.
   procedure Set_Environment_Upvalue (State : in out Compiler_State)
   with Global => null;

   --  Releases everything the state holds.
   procedure Release (State : in out Compiler_State)
   with
     Global => null,
     Post   =>
       Is_Released (State)
       and then Limit (Budget_Of (State)) = Limit (Budget_Of (State))'Old;

   --  Stops the compilation: the compiler's own logic went wrong, or, in a chunk with other
   --  errors, the tree is not what a correct chunk gives (no error is reported then).
   procedure Fail (State : in out Compiler_State)
   with Global => null, Post => Failed (State);

   --  Compiles a chunk with other errors: nothing from token Cut on is compiled (0 when the
   --  whole tree was parsed), scope errors are passed over, and only compile-time limit
   --  errors reached before Cut are reported, since PUC Lua raises them while it parses.
   procedure Set_Partial (State : in out Compiler_State; Cut : Natural)
   with Global => null;

   --  The chunk has other errors (Set_Partial).
   function Is_Partial (State : Compiler_State) return Boolean
   with Global => null;

   --  [puc llex.c:luaX_syntaxerror] Stops the compilation with a compile-time limit error,
   --  raised as PUC Lua raises it: at the current token, near it.
   procedure Raise_Error (State : in out Compiler_State; What : Problem; Function_Line : Natural)
   with Global => null, Post => Failed (State);

   --  [puc] lastline: the line of the token read last.
   function Last_Line (State : Compiler_State) return Line_Number
   with Global => null;

   --  The line of token Ordinal (1 for 0, the end of the chunk after the last).
   function Token_Line (State : Compiler_State; Ordinal : Natural) return Line_Number
   with Global => null;

   --  The ordinal of the token holding byte Position.
   function Token_At (State : Compiler_State; Position : Span_End) return Natural
   with Global => null;

   --  The open function.
   function Current (State : Compiler_State) return Function_Entry
   with Global => null;

   --  Replaces the open function's entry.
   procedure Set_Current (State : in out Compiler_State; Item : Function_Entry)
   with Global => null;

   --  [puc] fs->pc: the number of instructions of the open function.
   function PC (State : Compiler_State) return Natural
   with Global => null;

   --  Instruction Index of the open function (a default instruction if there is none).
   function Get (State : Compiler_State; Index : Natural) return Instruction
   with Global => null;

   --  Replaces instruction Index of the open function.
   procedure Put (State : in out Compiler_State; Index : Natural; Item : Instruction)
   with Global => null;

   --  Variable Index (absolute) of the variables array.
   function Variable (State : Compiler_State; Index : Natural) return Variable_Entry
   with Global => null;

   --  [puc lparser.c:getlocalvardesc] Local variable Index of the open function.
   function Local_Variable_Of (State : Compiler_State; Index : Natural) return Variable_Entry
   with Global => null;

   --  [puc lparser.c:reglevel] The number of registers the first Count variables of the open
   --  function use.
   function Register_Level (State : Compiler_State; Count : Natural) return Natural
   with Global => null, Post => Register_Level'Result <= 256;

   --  [puc lparser.c:luaY_nvarstack] The number of registers the active variables use.
   function Variables_On_Stack (State : Compiler_State) return Natural
   with Global => null, Post => Variables_On_Stack'Result <= 256;

   --  [puc lcode.c] The code generator. Each procedure is the lcode.c function named in its
   --  comment, on the open function.

   --  luaK_code with luaK_codeABCk: Result is the new instruction's program counter.
   procedure Code_ABC
     (State : in out Compiler_State;
      Operation : Opcode;
      A, B, C : Natural;
      K : Boolean;
      Result : out Natural)
   with Global => null;

   --  luaK_codeABx.
   procedure Code_ABx
     (State : in out Compiler_State; Operation : Opcode; A, Bx : Natural; Result : out Natural)
   with Global => null;

   --  luaK_fixline.
   procedure Fix_Line (State : in out Compiler_State; Line : Line_Number)
   with Global => null;

   --  luaK_nil.
   procedure Load_Nil (State : in out Compiler_State; From, Count : Natural)
   with Global => null;

   --  luaK_jump.
   procedure Jump (State : in out Compiler_State; Result : out Jump_List)
   with Global => null;

   --  luaK_ret.
   procedure Return_Values (State : in out Compiler_State; First : Natural; Count : Integer)
   with Global => null;

   --  luaK_getlabel.
   procedure Get_Label (State : in out Compiler_State; Result : out Natural)
   with Global => null;

   --  luaK_concat.
   procedure Concatenate_Jumps (State : in out Compiler_State; List : in out Jump_List;
                                Other : Jump_List)
   with Global => null;

   --  luaK_patchlist.
   procedure Patch_List (State : in out Compiler_State; List : Jump_List; Target : Natural)
   with Global => null;

   --  luaK_patchtohere.
   procedure Patch_To_Here (State : in out Compiler_State; List : Jump_List)
   with Global => null;

   --  luaK_checkstack.
   procedure Check_Stack (State : in out Compiler_State; Count : Natural)
   with Global => null;

   --  luaK_reserveregs.
   procedure Reserve_Registers (State : in out Compiler_State; Count : Natural)
   with Global => null;

   --  luaK_int.
   procedure Load_Integer (State : in out Compiler_State; Register : Natural;
                           Value : Interfaces.Integer_64)
   with Global => null;

   --  luaK_setreturns, with Count = Multiple_Results for luaK_setmultret.
   procedure Set_Returns (State : in out Compiler_State; Item : Expression; Count : Integer)
   with Global => null;

   --  luaK_setoneret.
   procedure Set_One_Return (State : in out Compiler_State; Item : in out Expression)
   with Global => null;

   --  luaK_dischargevars.
   procedure Discharge_Variables (State : in out Compiler_State; Item : in out Expression)
   with Global => null;

   --  luaK_exp2nextreg.
   procedure To_Next_Register (State : in out Compiler_State; Item : in out Expression)
   with Global => null;

   --  luaK_exp2anyreg: Register is where the value ends up.
   procedure To_Any_Register
     (State : in out Compiler_State; Item : in out Expression; Register : out Natural)
   with Global => null;

   --  luaK_exp2anyregup.
   procedure To_Any_Register_Or_Upvalue (State : in out Compiler_State;
                                         Item : in out Expression)
   with Global => null;

   --  luaK_exp2val.
   procedure To_Value (State : in out Compiler_State; Item : in out Expression)
   with Global => null;

   --  luaK_exp2const: the value of a constant expression, if it is one.
   procedure To_Constant
     (State : Compiler_State; Item : Expression; Value : out Constant_Value;
      Success : out Boolean)
   with Global => null;

   --  luaK_storevar.
   procedure Store_Variable
     (State : in out Compiler_State; Target : Expression; Value : in out Expression)
   with Global => null;

   --  luaK_self.
   procedure Self_Call
     (State : in out Compiler_State; Object : in out Expression; Key : in out Expression)
   with Global => null;

   --  luaK_indexed.
   procedure Indexed
     (State : in out Compiler_State; Table : in out Expression; Key_Value : Expression)
   with Global => null;

   --  luaK_goiftrue.
   procedure Go_If_True (State : in out Compiler_State; Item : in out Expression)
   with Global => null;

   --  luaK_goiffalse.
   procedure Go_If_False (State : in out Compiler_State; Item : in out Expression)
   with Global => null;

   --  luaK_prefix.
   procedure Prefix
     (State : in out Compiler_State;
      Operator : Operator_Kind;
      Item : in out Expression;
      Line : Line_Number)
   with Global => null;

   --  luaK_infix.
   procedure Infix
     (State : in out Compiler_State; Operator : Operator_Kind; Item : in out Expression)
   with Global => null;

   --  luaK_posfix.
   procedure Posfix
     (State : in out Compiler_State;
      Operator : Operator_Kind;
      Left : in out Expression;
      Right : in out Expression;
      Line : Line_Number)
   with Global => null;

   --  luaK_settablesize.
   procedure Set_Table_Size
     (State : in out Compiler_State; Index, Register, Array_Size, Hash_Size : Natural)
   with Global => null;

   --  luaK_setlist.
   procedure Set_List
     (State : in out Compiler_State; Base, Count : Natural; To_Store : Integer)
   with Global => null;

   --  luaK_finish.
   procedure Finish (State : in out Compiler_State)
   with Global => null;

   --  [puc lcode.c:luaK_code] Appends a bare instruction (luaK_code (fs, 0)).
   procedure Code_Raw (State : in out Compiler_State; Item : Instruction)
   with Global => null;

   --  Value as a jump list (an instruction's program counter).
   function As_Jump (Value : Natural) return Jump_List
   is (if Value <= Entry_Number'Last then Value else No_Jump);

   --  An expression of the given kind with nothing else.
   function Make (Kind : Expression_Kind; Info : Natural := 0) return Expression
   is ((Kind => Kind, Info => Info, others => <>));

   --  [puc lcode.c:hasjumps].
   function Has_Jumps (Item : Expression) return Boolean
   is (Item.True_List /= Item.False_List);

   --  [puc lparser.h:hasmultret].
   function Has_Multiple_Results (Item : Expression) return Boolean
   is (Item.Kind in Open_Call | Open_Vararg);

   --  [puc lparser.h:vkisvar] / vkisindexed.
   function Is_Indexed (Item : Expression) return Boolean
   is (Item.Kind in Indexed_Register .. Indexed_String);

private
   --  Clients see the state through the operations above, which keeps its representation
   --  (seventeen arrays and their pointers) out of their proofs.
   pragma Annotate (GNATprove, Hide_Info, "Private_Part");

   package Instruction_Arrays is new Pyro.Growable_Arrays
     (Index => Work_Position, Element_Type => Instruction, Default_Element => (others => <>),
      Element_Bytes => 12);
   package Line_Arrays is new Pyro.Growable_Arrays
     (Index => Work_Position, Element_Type => Line_Number, Default_Element => 1,
      Element_Bytes => 4);
   package Constant_Arrays is new Pyro.Growable_Arrays
     (Index => Work_Position, Element_Type => Constant_Value, Default_Element => (others => <>),
      Element_Bytes => 16);
   package Debug_Arrays is new Pyro.Growable_Arrays
     (Index => Work_Position, Element_Type => Local_Variable, Default_Element => (others => <>),
      Element_Bytes => 12);
   package Child_Arrays is new Pyro.Growable_Arrays
     (Index => Work_Position, Element_Type => Prototype_Index, Default_Element => No_Prototype,
      Element_Bytes => 4);
   package Upvalue_Arrays is new Pyro.Growable_Arrays
     (Index => Work_Position, Element_Type => Upvalue_Entry, Default_Element => (others => <>),
      Element_Bytes => 12);
   package Variable_Arrays is new Pyro.Growable_Arrays
     (Index => Work_Position, Element_Type => Variable_Entry, Default_Element => (others => <>),
      Element_Bytes => 32);
   package Label_Arrays is new Pyro.Growable_Arrays
     (Index => Work_Position, Element_Type => Label_Entry, Default_Element => (others => <>),
      Element_Bytes => 20);
   package Block_Arrays is new Pyro.Growable_Arrays
     (Index => Work_Position, Element_Type => Block_Entry, Default_Element => (others => <>),
      Element_Bytes => 16);
   package Function_Arrays is new Pyro.Growable_Arrays
     (Index => Work_Position, Element_Type => Function_Entry, Default_Element => (others => <>),
      Element_Bytes => 64);
   package Cache_Arrays is new Pyro.Growable_Arrays
     (Index => Work_Position, Element_Type => Cache_Entry, Default_Element => (others => <>),
      Element_Bytes => 24);
   package Token_Arrays is new Pyro.Growable_Arrays
     (Index => Work_Position, Element_Type => Token_Entry, Default_Element => (others => <>),
      Element_Bytes => 12);
   package Expression_Arrays is new Pyro.Growable_Arrays
     (Index => Work_Position, Element_Type => Expression, Default_Element => (others => <>),
      Element_Bytes => 64);
   package Node_Arrays is new Pyro.Growable_Arrays
     (Index => Work_Position, Element_Type => Node_Index, Default_Element => No_Node,
      Element_Bytes => 4);

   --  Everything the compiler works on. Failed is set by the first error, after which the
   --  compiler only unwinds; Error is the error unless it is an internal one.
   type Compiler_State is limited record
      Budget         : Memory_Budget := Create (0);
      Code           : Instruction_Arrays.Growable_Array;
      Lines          : Line_Arrays.Growable_Array;
      Constants      : Constant_Arrays.Growable_Array;
      Debug_Locals   : Debug_Arrays.Growable_Array;
      Children       : Child_Arrays.Growable_Array;
      Upvalues       : Upvalue_Arrays.Growable_Array;
      --  [puc] dyd->actvar: the first Variable_Count entries are the declared variables; the
      --  entries after them are left over from closed blocks, which PUC Lua still reads.
      Variables      : Variable_Arrays.Growable_Array;
      Variable_Count : Bounded_Count := 0;
      Labels         : Label_Arrays.Growable_Array;
      Gotos          : Label_Arrays.Growable_Array;
      Blocks         : Block_Arrays.Growable_Array;
      Functions      : Function_Arrays.Growable_Array;
      Cache          : Cache_Arrays.Growable_Array;
      Cache_Used     : Bounded_Count := 0;
      Tokens         : Token_Arrays.Growable_Array;
      --  The targets of the assignments being compiled, and the chains of operators and
      --  suffixes being walked.
      Targets        : Expression_Arrays.Growable_Array;
      Spine          : Node_Arrays.Growable_Array;
      --  A name token PUC Lua looked past before reading it (a field of a table constructor):
      --  reading it leaves lastline at the next token's line.
      Lookahead_Name : Natural := 0;
      --  Set_Partial: the chunk has other errors, and the first token not compiled.
      Partial        : Boolean := False;
      Cut            : Natural := 0;
      --  The token read last ([puc] lastline is its line); 0 before the first.
      Last_Token     : Bounded_Count := 0;
      Failed         : Boolean := False;
      Has_Error      : Boolean := False;
      Error          : Diagnostic := (others => <>);
      --  The names the compiler makes up.
      Environment_Name : Symbol_Index := No_Symbol;
      Break_Name       : Symbol_Index := No_Symbol;
      Self_Name        : Symbol_Index := No_Symbol;
      For_State_Name   : Symbol_Index := No_Symbol;
   end record;

end Pyro.Compiler.Code;
