--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  Lua 5.4's instruction set as typed records, compiled prototypes, and their validity.

with Interfaces;
with Pyro.Growable_Arrays;
with Pyro.Memory_Budgets; use Pyro.Memory_Budgets;
with Pyro.Sources;        use Pyro.Sources;
with Pyro.Symbols;        use Pyro.Symbols;

package Pyro.Bytecode with SPARK_Mode => On, Always_Terminates is

   --  [puc lopcodes.h:OpCode] The operations, in lopcodes.h's order (code generation relies on
   --  it, as lcode.c does). The comments give luac's name.
   type Opcode is
     (Move,                           --  MOVE
      Load_Integer,                   --  LOADI
      Load_Float,                     --  LOADF
      Load_Constant,                  --  LOADK
      Load_Constant_Extra,            --  LOADKX
      Load_False,                     --  LOADFALSE
      Load_False_Skip,                --  LFALSESKIP
      Load_True,                      --  LOADTRUE
      Load_Nil,                       --  LOADNIL
      Get_Upvalue,                    --  GETUPVAL
      Set_Upvalue,                    --  SETUPVAL
      Get_Table_Upvalue,              --  GETTABUP
      Get_Table,                      --  GETTABLE
      Get_Integer,                    --  GETI
      Get_Field,                      --  GETFIELD
      Set_Table_Upvalue,              --  SETTABUP
      Set_Table,                      --  SETTABLE
      Set_Integer,                    --  SETI
      Set_Field,                      --  SETFIELD
      New_Table,                      --  NEWTABLE
      Self,                           --  SELF
      Add_Integer,                    --  ADDI
      Add_Constant,                   --  ADDK
      Subtract_Constant,              --  SUBK
      Multiply_Constant,              --  MULK
      Modulo_Constant,                --  MODK
      Power_Constant,                 --  POWK
      Divide_Constant,                --  DIVK
      Floor_Divide_Constant,          --  IDIVK
      Bitwise_And_Constant,           --  BANDK
      Bitwise_Or_Constant,            --  BORK
      Bitwise_Exclusive_Or_Constant,  --  BXORK
      Shift_Right_Integer,            --  SHRI
      Shift_Left_Integer,             --  SHLI
      Add,                            --  ADD
      Subtract,                       --  SUB
      Multiply,                       --  MUL
      Modulo,                         --  MOD
      Power,                          --  POW
      Divide,                         --  DIV
      Floor_Divide,                   --  IDIV
      Bitwise_And,                    --  BAND
      Bitwise_Or,                     --  BOR
      Bitwise_Exclusive_Or,           --  BXOR
      Shift_Left,                     --  SHL
      Shift_Right,                    --  SHR
      Metamethod_Binary,              --  MMBIN
      Metamethod_Binary_Integer,      --  MMBINI
      Metamethod_Binary_Constant,     --  MMBINK
      Negate,                         --  UNM
      Bitwise_Not,                    --  BNOT
      Logical_Not,                    --  NOT
      Length,                         --  LEN
      Concatenate,                    --  CONCAT
      Close,                          --  CLOSE
      To_Be_Closed,                   --  TBC
      Jump,                           --  JMP
      Equal,                          --  EQ
      Less_Than,                      --  LT
      Less_Equal,                     --  LE
      Equal_Constant,                 --  EQK
      Equal_Integer,                  --  EQI
      Less_Than_Integer,              --  LTI
      Less_Equal_Integer,             --  LEI
      Greater_Than_Integer,           --  GTI
      Greater_Equal_Integer,          --  GEI
      Test,                           --  TEST
      Test_Set,                       --  TESTSET
      Call,                           --  CALL
      Tail_Call,                      --  TAILCALL
      Return_Values,                  --  RETURN
      Return_None,                    --  RETURN0
      Return_One,                     --  RETURN1
      For_Loop,                       --  FORLOOP
      For_Prepare,                    --  FORPREP
      Generic_For_Prepare,            --  TFORPREP
      Generic_For_Call,               --  TFORCALL
      Generic_For_Loop,               --  TFORLOOP
      Set_List,                       --  SETLIST
      Closure,                        --  CLOSURE
      Vararg,                         --  VARARG
      Vararg_Prepare,                 --  VARARGPREP
      Extra_Argument);                --  EXTRAARG

   --  [puc lopcodes.h:OpMode] Which operands an instruction has besides its opcode.
   type Instruction_Format is
     (Format_ABC,    --  A, B, C and k
      Format_ABx,    --  A and the unsigned Bx
      Format_AsBx,   --  A and the signed sBx
      Format_Ax,     --  the unsigned Ax
      Format_sJ);    --  the signed jump offset sJ

   --  [puc lopcodes.c:luaP_opmodes] The format of each opcode.
   function Format_Of (Operation : Opcode) return Instruction_Format
   is (case Operation is
         when Load_Integer | Load_Float => Format_AsBx,
         when Load_Constant | Load_Constant_Extra | For_Loop | For_Prepare
            | Generic_For_Prepare | Generic_For_Loop | Closure => Format_ABx,
         when Extra_Argument => Format_Ax,
         when Jump => Format_sJ,
         when others => Format_ABC);

   --  An 8-bit operand: A, B or C. Signed operands (sB, sC) are kept excess Offset_sC.
   type Byte is range 0 .. 255;

   --  [puc lopcodes.h] Limits and offsets of the operands.
   Maximum_Bx     : constant := 2 ** 17 - 1;
   Offset_sBx     : constant := 2 ** 16 - 1;
   Maximum_Ax     : constant := 2 ** 25 - 1;
   Offset_sJ      : constant := 2 ** 24 - 1;
   Offset_sC      : constant := 127;
   Maximum_C      : constant := 255;

   --  The wide operand: Bx, sBx (excess Offset_sBx), Ax, or sJ (excess Offset_sJ), as the
   --  opcode's format says.
   type Wide_Argument is range 0 .. Maximum_Ax;

   --  One instruction. The operands an opcode does not have are 0 (and K False).
   type Instruction is record
      Operation : Opcode := Move;
      A         : Byte := 0;
      B         : Byte := 0;
      C         : Byte := 0;
      K         : Boolean := False;
      Wide      : Wide_Argument := 0;
   end record;

   --  [puc lopcodes.h:MAXREGS] The most registers a function can use.
   Maximum_Registers : constant := 255;

   --  [puc ltm.h:TMS] The metamethod events of binary arithmetic and bitwise operations, as
   --  C operands of MMBIN, MMBINI and MMBINK.
   First_Binary_Event : constant Byte := 6;   --  TM_ADD
   Last_Binary_Event  : constant Byte := 17;  --  TM_SHR

   --  The kind of a constant. Strings are short (at most 40 bytes, LUAI_MAXSHORTLEN) or long,
   --  since some instructions take only short strings.
   type Constant_Kind is
     (Nil_Constant, False_Constant, True_Constant, Integer_Constant, Float_Constant,
      Short_String_Constant, Long_String_Constant);

   subtype String_Constant_Kind is Constant_Kind
     range Short_String_Constant .. Long_String_Constant;

   --  [puc llimits.h:LUAI_MAXSHORTLEN] The longest short string.
   Maximum_Short_String : constant := 40;

   --  A constant: an integer (two's complement bits) or float (IEEE 754 bits) in Bits, a
   --  string as the symbol of its bytes.
   type Constant_Value is record
      Kind   : Constant_Kind := Nil_Constant;
      Bits   : Interfaces.Unsigned_64 := 0;
      Symbol : Symbol_Index := No_Symbol;
   end record;

   --  [puc lobject.h:Upvaldesc] Where a closure finds an upvalue when it is created: a
   --  register of the enclosing function (In_Stack) or one of its upvalues.
   type Upvalue_Description is record
      Name     : Symbol_Index := No_Symbol;
      In_Stack : Boolean := False;
      Index    : Byte := 0;
   end record;

   --  The most instructions, constants, upvalue descriptions, local variable records and
   --  nested prototypes a chunk holds, each.
   Maximum_Entries : constant := 2 ** 28;

   --  A count of entries of one prototype, and a 0-based number of an entry (an instruction's
   --  program counter, a constant's index K[n], ...).
   subtype Entry_Count is Natural range 0 .. Maximum_Entries;
   subtype Entry_Number is Natural range 0 .. Maximum_Entries - 1;

   --  [puc lobject.h:LocVar] A local variable, for debug information: it is active from
   --  instruction Start_PC up to, not including, End_PC.
   type Local_Variable is record
      Name     : Symbol_Index := No_Symbol;
      Start_PC : Entry_Count := 0;
      End_PC   : Entry_Count := 0;
   end record;

   --  A prototype of a chunk. Nested prototypes come before their parent; the main function
   --  is the last.
   type Prototype_Index is range 0 .. Maximum_Entries;
   No_Prototype : constant Prototype_Index := 0;

   --  The facts of a prototype besides its arrays. Line_Defined is 0 for the main function.
   type Prototype_Header is record
      Parameter_Count   : Byte := 0;
      Is_Vararg         : Boolean := False;
      Stack_Size        : Byte := 2;
      Line_Defined      : Natural := 0;
      Last_Line_Defined : Natural := 0;
   end record;

   --  The prototypes of a compiled chunk. It owns heap memory: release it with Clear.
   type Chunk is limited private
   with
     Default_Initial_Condition => Prototype_Count (Chunk) = 0 and then Is_Released (Chunk);

   --  Every prototype's arrays lie inside the chunk's, and nested prototypes come before
   --  their parent. Every operation keeps this.
   function Is_Well_Formed (Item : Chunk) return Boolean
   with Global => null;

   --  The number of finished prototypes.
   function Prototype_Count (Item : Chunk) return Prototype_Index
   with Global => null;

   --  The facts of prototype P.
   function Header (Item : Chunk; P : Prototype_Index) return Prototype_Header
   with Global => null, Pre => Is_Well_Formed (Item) and then P in 1 .. Prototype_Count (Item);

   --  The number of instructions of prototype P.
   function Code_Length (Item : Chunk; P : Prototype_Index) return Entry_Count
   with Global => null, Pre => Is_Well_Formed (Item) and then P in 1 .. Prototype_Count (Item);

   --  The number of constants of prototype P.
   function Constant_Count (Item : Chunk; P : Prototype_Index) return Entry_Count
   with Global => null, Pre => Is_Well_Formed (Item) and then P in 1 .. Prototype_Count (Item);

   --  The number of upvalues of prototype P.
   function Upvalue_Count (Item : Chunk; P : Prototype_Index) return Entry_Count
   with Global => null, Pre => Is_Well_Formed (Item) and then P in 1 .. Prototype_Count (Item);

   --  The number of local variable records of prototype P.
   function Local_Count (Item : Chunk; P : Prototype_Index) return Entry_Count
   with Global => null, Pre => Is_Well_Formed (Item) and then P in 1 .. Prototype_Count (Item);

   --  The number of prototypes nested directly in prototype P.
   function Child_Count (Item : Chunk; P : Prototype_Index) return Entry_Count
   with Global => null, Pre => Is_Well_Formed (Item) and then P in 1 .. Prototype_Count (Item);

   --  The opcode of instruction PC of prototype P.
   function Opcode_At (Item : Chunk; P : Prototype_Index; PC : Entry_Number) return Opcode
   with
     Global => null,
     Pre    =>
       Is_Well_Formed (Item)
       and then P in 1 .. Prototype_Count (Item)
       and then PC < Code_Length (Item, P);

   --  The source line of instruction PC of prototype P.
   function Line_At (Item : Chunk; P : Prototype_Index; PC : Entry_Number) return Line_Number
   with
     Global => null,
     Pre    =>
       Is_Well_Formed (Item)
       and then P in 1 .. Prototype_Count (Item)
       and then PC < Code_Length (Item, P);

   --  Constant Number (K[Number]) of prototype P.
   function Constant_At
     (Item : Chunk; P : Prototype_Index; Number : Entry_Number) return Constant_Value
   with
     Global => null,
     Pre    =>
       Is_Well_Formed (Item)
       and then P in 1 .. Prototype_Count (Item)
       and then Number < Constant_Count (Item, P);

   --  Upvalue Number of prototype P.
   function Upvalue_At
     (Item : Chunk; P : Prototype_Index; Number : Entry_Number) return Upvalue_Description
   with
     Global => null,
     Pre    =>
       Is_Well_Formed (Item)
       and then P in 1 .. Prototype_Count (Item)
       and then Number < Upvalue_Count (Item, P);

   --  Local variable record Number of prototype P.
   function Local_At
     (Item : Chunk; P : Prototype_Index; Number : Entry_Number) return Local_Variable
   with
     Global => null,
     Pre    =>
       Is_Well_Formed (Item)
       and then P in 1 .. Prototype_Count (Item)
       and then Number < Local_Count (Item, P);

   --  Nested prototype Number of prototype P: an earlier prototype (No_Prototype only in a
   --  chunk that is not valid).
   function Child_At
     (Item : Chunk; P : Prototype_Index; Number : Entry_Number) return Prototype_Index
   with
     Global => null,
     Pre    =>
       Is_Well_Formed (Item)
       and then P in 1 .. Prototype_Count (Item)
       and then Number < Child_Count (Item, P),
     Post   => Child_At'Result < P;

   --  Register Value is in prototype P's frame.
   function Is_Register (Item : Chunk; P : Prototype_Index; Value : Integer) return Boolean
   is (Value in 0 .. Natural (Header (Item, P).Stack_Size) - 1)
   with Pre => Is_Well_Formed (Item) and then P in 1 .. Prototype_Count (Item);

   --  Constant Number of prototype P exists and has one of the kinds First .. Last.
   function Is_Constant
     (Item  : Chunk;
      P     : Prototype_Index;
      Number : Integer;
      First : Constant_Kind := Constant_Kind'First;
      Last  : Constant_Kind := Constant_Kind'Last) return Boolean
   is (Number in 0 .. Entry_Number'Last
       and then Number < Constant_Count (Item, P)
       and then Constant_At (Item, P, Number).Kind in First .. Last)
   with Pre => Is_Well_Formed (Item) and then P in 1 .. Prototype_Count (Item);

   --  RK(C): a constant when K is set, a register otherwise.
   function Is_Register_Or_Constant
     (Item : Chunk; P : Prototype_Index; Value : Byte; K : Boolean) return Boolean
   is (if K then Is_Constant (Item, P, Natural (Value))
       else Is_Register (Item, P, Natural (Value)))
   with Pre => Is_Well_Formed (Item) and then P in 1 .. Prototype_Count (Item);

   --  Instruction PC + 1 exists and has opcode Operation.
   function Is_Followed_By
     (Item : Chunk; P : Prototype_Index; PC : Entry_Number; Operation : Opcode) return Boolean
   is (PC + 1 < Code_Length (Item, P) and then Opcode_At (Item, P, PC + 1) = Operation)
   with
     Pre =>
       Is_Well_Formed (Item)
       and then P in 1 .. Prototype_Count (Item)
       and then PC < Code_Length (Item, P);

   --  Instruction PC + 2 exists, so an instruction can skip the one after it.
   function Can_Skip (Item : Chunk; P : Prototype_Index; PC : Entry_Number) return Boolean
   is (PC + 2 < Code_Length (Item, P))
   with Pre => Is_Well_Formed (Item) and then P in 1 .. Prototype_Count (Item);

   --  Instruction PC - 1 exists and sets the top of the stack for the next instruction (a call
   --  or vararg with all results, or a tail call: lopcodes.h's isOT).
   function Follows_Open_Results
     (Item : Chunk; P : Prototype_Index; PC : Entry_Number) return Boolean
   with
     Global => null,
     Pre    =>
       Is_Well_Formed (Item)
       and then P in 1 .. Prototype_Count (Item)
       and then PC < Code_Length (Item, P);

   --  Target is an instruction of prototype P that a jump may go to: inside the code, and
   --  neither an extra argument nor a metamethod fallback (those depend on the instruction
   --  before them).
   function Is_Jump_Target (Item : Chunk; P : Prototype_Index; Target : Integer) return Boolean
   is (Target in 0 .. Code_Length (Item, P) - 1
       and then Opcode_At (Item, P, Target) not in Extra_Argument | Metamethod_Binary
                                                 | Metamethod_Binary_Integer
                                                 | Metamethod_Binary_Constant)
   with Pre => Is_Well_Formed (Item) and then P in 1 .. Prototype_Count (Item);

   --  The arithmetic and bitwise opcodes that a metamethod fallback follows.
   subtype Arithmetic_Opcode is Opcode range Add_Integer .. Shift_Right;

   --  The opcodes that compare or test and skip the jump after them when the test fails.
   subtype Test_Opcode is Opcode range Equal .. Test_Set;

   --  [puc lopcodes.h, lvm.c] What instruction Item at PC of prototype P needs to be safe to
   --  execute without runtime checks: its registers are in the frame, its constants,
   --  upvalues and prototypes exist with the kinds it needs, its jumps land on instructions,
   --  and the instructions it is paired with in the VM are in place.
   function Instruction_Valid
     (Chunk : Bytecode.Chunk; P : Prototype_Index; PC : Entry_Number; Item : Instruction)
      return Boolean
   is (case Item.Operation is
         when Move | Negate | Bitwise_Not | Logical_Not | Length =>
           Is_Register (Chunk, P, Integer (Item.A))
           and then Is_Register (Chunk, P, Integer (Item.B)),
         when Load_Integer | Load_Float =>
           Is_Register (Chunk, P, Integer (Item.A)) and then Item.Wide <= Maximum_Bx,
         when Load_Constant =>
           Is_Register (Chunk, P, Integer (Item.A))
           and then Is_Constant (Chunk, P, Integer (Item.Wide)),
         when Load_Constant_Extra =>
           Is_Register (Chunk, P, Integer (Item.A))
           and then Is_Followed_By (Chunk, P, PC, Extra_Argument)
           and then Can_Skip (Chunk, P, PC),
         when Load_False | Load_True | To_Be_Closed | Return_One =>
           Is_Register (Chunk, P, Integer (Item.A)),
         when Load_False_Skip =>
           Is_Register (Chunk, P, Integer (Item.A)) and then Can_Skip (Chunk, P, PC),
         when Load_Nil =>
           Is_Register (Chunk, P, Integer (Item.A) + Integer (Item.B)),
         when Get_Upvalue | Set_Upvalue =>
           Is_Register (Chunk, P, Integer (Item.A))
           and then Integer (Item.B) < Upvalue_Count (Chunk, P),
         when Get_Table_Upvalue =>
           Is_Register (Chunk, P, Integer (Item.A))
           and then Integer (Item.B) < Upvalue_Count (Chunk, P)
           and then Is_Constant (Chunk, P, Integer (Item.C),
                                 Short_String_Constant, Short_String_Constant),
         when Get_Table =>
           Is_Register (Chunk, P, Integer (Item.A))
           and then Is_Register (Chunk, P, Integer (Item.B))
           and then Is_Register (Chunk, P, Integer (Item.C)),
         when Get_Integer =>
           Is_Register (Chunk, P, Integer (Item.A))
           and then Is_Register (Chunk, P, Integer (Item.B)),
         when Get_Field =>
           Is_Register (Chunk, P, Integer (Item.A))
           and then Is_Register (Chunk, P, Integer (Item.B))
           and then Is_Constant (Chunk, P, Integer (Item.C),
                                 Short_String_Constant, Short_String_Constant),
         when Set_Table_Upvalue =>
           Integer (Item.A) < Upvalue_Count (Chunk, P)
           and then Is_Constant (Chunk, P, Integer (Item.B),
                                 Short_String_Constant, Short_String_Constant)
           and then Is_Register_Or_Constant (Chunk, P, Item.C, Item.K),
         when Set_Table =>
           Is_Register (Chunk, P, Integer (Item.A))
           and then Is_Register (Chunk, P, Integer (Item.B))
           and then Is_Register_Or_Constant (Chunk, P, Item.C, Item.K),
         when Set_Integer =>
           Is_Register (Chunk, P, Integer (Item.A))
           and then Is_Register_Or_Constant (Chunk, P, Item.C, Item.K),
         when Set_Field =>
           Is_Register (Chunk, P, Integer (Item.A))
           and then Is_Constant (Chunk, P, Integer (Item.B),
                                 Short_String_Constant, Short_String_Constant)
           and then Is_Register_Or_Constant (Chunk, P, Item.C, Item.K),
         when New_Table =>
           Is_Register (Chunk, P, Integer (Item.A))
           and then Is_Followed_By (Chunk, P, PC, Extra_Argument)
           and then Can_Skip (Chunk, P, PC),
         when Self =>
           Is_Register (Chunk, P, Integer (Item.A) + 1)
           and then Is_Register (Chunk, P, Integer (Item.B))
           and then (if Item.K
                     then Is_Constant (Chunk, P, Integer (Item.C),
                                       Short_String_Constant, Long_String_Constant)
                     else Is_Register (Chunk, P, Integer (Item.C))),
         when Add_Integer | Shift_Right_Integer | Shift_Left_Integer =>
           Is_Register (Chunk, P, Integer (Item.A))
           and then Is_Register (Chunk, P, Integer (Item.B))
           and then Is_Followed_By (Chunk, P, PC, Metamethod_Binary_Integer)
           and then Can_Skip (Chunk, P, PC),
         when Add_Constant .. Floor_Divide_Constant =>
           Is_Register (Chunk, P, Integer (Item.A))
           and then Is_Register (Chunk, P, Integer (Item.B))
           and then Is_Constant (Chunk, P, Integer (Item.C), Integer_Constant, Float_Constant)
           and then Is_Followed_By (Chunk, P, PC, Metamethod_Binary_Constant)
           and then Can_Skip (Chunk, P, PC),
         when Bitwise_And_Constant .. Bitwise_Exclusive_Or_Constant =>
           Is_Register (Chunk, P, Integer (Item.A))
           and then Is_Register (Chunk, P, Integer (Item.B))
           and then Is_Constant (Chunk, P, Integer (Item.C), Integer_Constant, Integer_Constant)
           and then Is_Followed_By (Chunk, P, PC, Metamethod_Binary_Constant)
           and then Can_Skip (Chunk, P, PC),
         when Add .. Shift_Right =>
           Is_Register (Chunk, P, Integer (Item.A))
           and then Is_Register (Chunk, P, Integer (Item.B))
           and then Is_Register (Chunk, P, Integer (Item.C))
           and then Is_Followed_By (Chunk, P, PC, Metamethod_Binary)
           and then Can_Skip (Chunk, P, PC),
         when Metamethod_Binary =>
           Is_Register (Chunk, P, Integer (Item.A))
           and then Is_Register (Chunk, P, Integer (Item.B))
           and then Item.C in First_Binary_Event .. Last_Binary_Event
           and then PC > 0
           and then Opcode_At (Chunk, P, PC - 1) in Arithmetic_Opcode,
         when Metamethod_Binary_Integer =>
           Is_Register (Chunk, P, Integer (Item.A))
           and then Item.C in First_Binary_Event .. Last_Binary_Event
           and then PC > 0
           and then Opcode_At (Chunk, P, PC - 1) in Arithmetic_Opcode,
         when Metamethod_Binary_Constant =>
           Is_Register (Chunk, P, Integer (Item.A))
           and then Is_Constant (Chunk, P, Integer (Item.B))
           and then Item.C in First_Binary_Event .. Last_Binary_Event
           and then PC > 0
           and then Opcode_At (Chunk, P, PC - 1) in Arithmetic_Opcode,
         when Concatenate =>
           Item.B >= 1 and then Is_Register (Chunk, P, Integer (Item.A) + Integer (Item.B) - 1),
         when Close =>
           Integer (Item.A) <= Integer (Header (Chunk, P).Stack_Size),
         when Jump =>
           Is_Jump_Target (Chunk, P, PC + 1 + Integer (Item.Wide) - Offset_sJ),
         when Equal | Less_Than | Less_Equal | Test_Set =>
           Is_Register (Chunk, P, Integer (Item.A))
           and then Is_Register (Chunk, P, Integer (Item.B))
           and then Is_Followed_By (Chunk, P, PC, Jump)
           and then Can_Skip (Chunk, P, PC),
         when Equal_Constant =>
           Is_Register (Chunk, P, Integer (Item.A))
           and then Is_Constant (Chunk, P, Integer (Item.B))
           and then Is_Followed_By (Chunk, P, PC, Jump)
           and then Can_Skip (Chunk, P, PC),
         when Equal_Integer .. Greater_Equal_Integer | Test =>
           Is_Register (Chunk, P, Integer (Item.A))
           and then Is_Followed_By (Chunk, P, PC, Jump)
           and then Can_Skip (Chunk, P, PC),
         when Call =>
           Is_Register (Chunk, P, Integer (Item.A))
           and then (if Item.B = 0 then Follows_Open_Results (Chunk, P, PC)
                     else Is_Register (Chunk, P, Integer (Item.A) + Integer (Item.B) - 1))
           and then (Item.C <= 1
                     or else Is_Register (Chunk, P, Integer (Item.A) + Integer (Item.C) - 2)),
         when Tail_Call =>
           Is_Register (Chunk, P, Integer (Item.A))
           and then (if Item.B = 0 then Follows_Open_Results (Chunk, P, PC)
                     else Is_Register (Chunk, P, Integer (Item.A) + Integer (Item.B) - 1)),
         when Return_Values =>
           Integer (Item.A) <= Integer (Header (Chunk, P).Stack_Size)
           and then (if Item.B = 0 then Follows_Open_Results (Chunk, P, PC)
                     else Item.B = 1
                          or else Is_Register (Chunk, P, Integer (Item.A) + Integer (Item.B) - 2)),
         when Return_None =>
           True,
         when For_Loop =>
           Is_Register (Chunk, P, Integer (Item.A) + 3)
           and then Item.Wide <= Maximum_Bx
           and then Is_Jump_Target (Chunk, P, PC + 1 - Integer (Item.Wide)),
         when For_Prepare =>
           Is_Register (Chunk, P, Integer (Item.A) + 3)
           and then Item.Wide <= Maximum_Bx
           and then Is_Jump_Target (Chunk, P, PC + 2 + Integer (Item.Wide)),
         when Generic_For_Prepare =>
           Is_Register (Chunk, P, Integer (Item.A) + 3)
           and then Item.Wide <= Maximum_Bx
           and then Is_Jump_Target (Chunk, P, PC + 1 + Integer (Item.Wide))
           and then Opcode_At (Chunk, P, PC + 1 + Integer (Item.Wide)) = Generic_For_Call,
         when Generic_For_Call =>
           Is_Register (Chunk, P, Integer (Item.A) + 6)
           and then Is_Register (Chunk, P, Integer (Item.A) + 3 + Integer (Item.C))
           and then Is_Followed_By (Chunk, P, PC, Generic_For_Loop),
         when Generic_For_Loop =>
           Is_Register (Chunk, P, Integer (Item.A) + 4)
           and then Item.Wide <= Maximum_Bx
           and then Is_Jump_Target (Chunk, P, PC + 1 - Integer (Item.Wide)),
         when Set_List =>
           Is_Register (Chunk, P, Integer (Item.A))
           and then (if Item.B = 0 then Follows_Open_Results (Chunk, P, PC)
                     else Is_Register (Chunk, P, Integer (Item.A) + Integer (Item.B)))
           and then (if Item.K
                     then Is_Followed_By (Chunk, P, PC, Extra_Argument)
                          and then Can_Skip (Chunk, P, PC)),
         when Closure =>
           Is_Register (Chunk, P, Integer (Item.A))
           and then Integer (Item.Wide) < Child_Count (Chunk, P),
         when Vararg =>
           Header (Chunk, P).Is_Vararg
           and then Is_Register (Chunk, P, Integer (Item.A))
           and then (Item.C <= 1
                     or else Is_Register (Chunk, P, Integer (Item.A) + Integer (Item.C) - 2)),
         when Vararg_Prepare =>
           Header (Chunk, P).Is_Vararg
           and then PC = 0
           and then Item.A = Header (Chunk, P).Parameter_Count,
         when Extra_Argument =>
           PC > 0
           and then Opcode_At (Chunk, P, PC - 1) in Load_Constant_Extra | New_Table | Set_List
           and then (if Opcode_At (Chunk, P, PC - 1) = Load_Constant_Extra
                     then Is_Constant (Chunk, P, Integer (Item.Wide))))
   with
     Pre =>
       Is_Well_Formed (Chunk)
       and then P in 1 .. Prototype_Count (Chunk)
       and then PC < Code_Length (Chunk, P);

   --  The definition is only needed where the facts are used (the VM), not where validity is
   --  checked or carried along; hiding it keeps it out of every other proof.
   pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Instruction_Valid);

   --  [proof] Every prototype of the chunk can run on Pyro's VM without runtime checks: each
   --  instruction satisfies Instruction_Valid; the last instruction cannot fall through (a
   --  return or a jump); a vararg function starts with VARARGPREP; the frame has the registers
   --  0 and 1 and every parameter; and every upvalue a nested prototype captures is a register
   --  or an upvalue of its parent. It is executable: the compiler checks what it built with it.
   function Is_Valid (Item : Chunk) return Boolean
   with Global => null;

   --  Instruction PC of prototype P. Of a valid chunk, it satisfies Instruction_Valid.
   function Instruction_At
     (Item : Chunk; P : Prototype_Index; PC : Entry_Number) return Instruction
   with
     Global => null,
     Pre    =>
       Is_Well_Formed (Item)
       and then P in 1 .. Prototype_Count (Item)
       and then PC < Code_Length (Item, P),
     Post   =>
       Instruction_At'Result.Operation = Opcode_At (Item, P, PC)
       and then (if Is_Valid (Item) then Instruction_Valid (Item, P, PC, Instruction_At'Result));

   --  Facts of every prototype of a valid chunk.
   procedure Lemma_Valid_Prototype (Item : Chunk; P : Prototype_Index)
   with
     Ghost,
     Global => null,
     Pre    =>
       Is_Well_Formed (Item) and then Is_Valid (Item) and then P in 1 .. Prototype_Count (Item),
     Post   =>
       Code_Length (Item, P) > 0
       and then Opcode_At (Item, P, Code_Length (Item, P) - 1)
                  in Return_Values | Return_None | Return_One | Jump
       and then Header (Item, P).Stack_Size >= 2
       and then Header (Item, P).Parameter_Count <= Header (Item, P).Stack_Size
       and then (if Header (Item, P).Is_Vararg then Opcode_At (Item, P, 0) = Vararg_Prepare);

   --  Building a chunk: the arrays of the next prototype are appended entry by entry, then
   --  Finish_Prototype makes them a prototype. Each operation leaves the chunk unchanged
   --  when Budget cannot pay (Success False).

   --  Appends an instruction, with its source line, to the next prototype.
   procedure Append_Instruction
     (Item    : in out Chunk;
      Budget  : in out Memory_Budget;
      Value   : Instruction;
      Line    : Line_Number;
      Success : out Boolean)
   with
     Global => null,
     Pre    => Is_Well_Formed (Item),
     Post   =>
       Is_Well_Formed (Item)
       and then Prototype_Count (Item) = Prototype_Count (Item)'Old
       and then Limit (Budget) = Limit (Budget)'Old;

   --  Appends a constant to the next prototype.
   procedure Append_Constant
     (Item    : in out Chunk;
      Budget  : in out Memory_Budget;
      Value   : Constant_Value;
      Success : out Boolean)
   with
     Global => null,
     Pre    => Is_Well_Formed (Item),
     Post   =>
       Is_Well_Formed (Item)
       and then Prototype_Count (Item) = Prototype_Count (Item)'Old
       and then Limit (Budget) = Limit (Budget)'Old;

   --  Appends an upvalue description to the next prototype.
   procedure Append_Upvalue
     (Item    : in out Chunk;
      Budget  : in out Memory_Budget;
      Value   : Upvalue_Description;
      Success : out Boolean)
   with
     Global => null,
     Pre    => Is_Well_Formed (Item),
     Post   =>
       Is_Well_Formed (Item)
       and then Prototype_Count (Item) = Prototype_Count (Item)'Old
       and then Limit (Budget) = Limit (Budget)'Old;

   --  Appends a local variable record to the next prototype.
   procedure Append_Local
     (Item    : in out Chunk;
      Budget  : in out Memory_Budget;
      Value   : Local_Variable;
      Success : out Boolean)
   with
     Global => null,
     Pre    => Is_Well_Formed (Item),
     Post   =>
       Is_Well_Formed (Item)
       and then Prototype_Count (Item) = Prototype_Count (Item)'Old
       and then Limit (Budget) = Limit (Budget)'Old;

   --  Appends an existing prototype as a child of the next prototype.
   procedure Append_Child
     (Item    : in out Chunk;
      Budget  : in out Memory_Budget;
      Child   : Prototype_Index;
      Success : out Boolean)
   with
     Global => null,
     Pre    => Is_Well_Formed (Item) and then Child in 1 .. Prototype_Count (Item),
     Post   =>
       Is_Well_Formed (Item)
       and then Prototype_Count (Item) = Prototype_Count (Item)'Old
       and then Limit (Budget) = Limit (Budget)'Old;

   --  Makes everything appended since the last prototype a new prototype, the last one.
   procedure Finish_Prototype
     (Item    : in out Chunk;
      Budget  : in out Memory_Budget;
      Facts   : Prototype_Header;
      Success : out Boolean)
   with
     Global => null,
     Pre    => Is_Well_Formed (Item),
     Post   =>
       Is_Well_Formed (Item)
       and then Limit (Budget) = Limit (Budget)'Old
       and then (if Success then Prototype_Count (Item) = Prototype_Count (Item)'Old + 1
                 else Prototype_Count (Item) = Prototype_Count (Item)'Old);

   --  Checks the chunk: Valid when it is valid; otherwise it is emptied.
   procedure Validate (Item : in out Chunk; Budget : in out Memory_Budget; Valid : out Boolean)
   with
     Global => null,
     Post   =>
       Is_Well_Formed (Item)
       and then Limit (Budget) = Limit (Budget)'Old
       and then (if Valid then Is_Valid (Item) else Prototype_Count (Item) = 0)
       and then (Prototype_Count (Item) = 0 or else Is_Valid (Item));

   --  Releases the chunk's memory; it is then empty.
   procedure Clear (Item : in out Chunk; Budget : in out Memory_Budget)
   with
     Global => null,
     Post   =>
       Is_Well_Formed (Item)
       and then Prototype_Count (Item) = 0
       and then Is_Released (Item)
       and then Limit (Budget) = Limit (Budget)'Old;

   --  True when the chunk holds no heap memory.
   function Is_Released (Item : Chunk) return Boolean
   with Global => null;

private

   subtype Arena_Position is Prototype_Index range 1 .. Prototype_Index'Last;

   --  A prototype: where its arrays start in the chunk's arenas (the number of entries before
   --  them), how long they are, and its facts.
   type Prototype_Entry is record
      Facts          : Prototype_Header := (others => <>);
      Code_Base      : Entry_Count := 0;
      Code_Length    : Entry_Count := 0;
      Constant_Base  : Entry_Count := 0;
      Constant_Count : Entry_Count := 0;
      Upvalue_Base   : Entry_Count := 0;
      Upvalue_Count  : Entry_Count := 0;
      Local_Base     : Entry_Count := 0;
      Local_Count    : Entry_Count := 0;
      Child_Base     : Entry_Count := 0;
      Child_Count    : Entry_Count := 0;
   end record;

   package Instruction_Arrays is new Pyro.Growable_Arrays
     (Index => Arena_Position, Element_Type => Instruction, Default_Element => (others => <>),
      Element_Bytes => 12);
   package Line_Arrays is new Pyro.Growable_Arrays
     (Index => Arena_Position, Element_Type => Line_Number, Default_Element => 1,
      Element_Bytes => 4);
   package Constant_Arrays is new Pyro.Growable_Arrays
     (Index => Arena_Position, Element_Type => Constant_Value, Default_Element => (others => <>),
      Element_Bytes => 16);
   package Upvalue_Arrays is new Pyro.Growable_Arrays
     (Index => Arena_Position, Element_Type => Upvalue_Description,
      Default_Element => (others => <>), Element_Bytes => 8);
   package Local_Arrays is new Pyro.Growable_Arrays
     (Index => Arena_Position, Element_Type => Local_Variable, Default_Element => (others => <>),
      Element_Bytes => 12);
   package Child_Arrays is new Pyro.Growable_Arrays
     (Index => Arena_Position, Element_Type => Prototype_Index, Default_Element => No_Prototype,
      Element_Bytes => 4);
   package Prototype_Arrays is new Pyro.Growable_Arrays
     (Index => Arena_Position, Element_Type => Prototype_Entry, Default_Element => (others => <>),
      Element_Bytes => 64);

   type Chunk is limited record
      Instructions : Instruction_Arrays.Growable_Array;
      Lines        : Line_Arrays.Growable_Array;
      Constants    : Constant_Arrays.Growable_Array;
      Upvalues     : Upvalue_Arrays.Growable_Array;
      Locals       : Local_Arrays.Growable_Array;
      Children     : Child_Arrays.Growable_Array;
      Prototypes   : Prototype_Arrays.Growable_Array;
      --  The entries before those of the next prototype, in each arena.
      Pending_Code      : Entry_Count := 0;
      Pending_Constants : Entry_Count := 0;
      Pending_Upvalues  : Entry_Count := 0;
      Pending_Locals    : Entry_Count := 0;
      Pending_Children  : Entry_Count := 0;
   end record;

   function Prototype_Count (Item : Chunk) return Prototype_Index
   is (Prototype_Arrays.Length (Item.Prototypes));

   function Is_Released (Item : Chunk) return Boolean
   is (Instruction_Arrays.Is_Released (Item.Instructions)
       and then Line_Arrays.Is_Released (Item.Lines)
       and then Constant_Arrays.Is_Released (Item.Constants)
       and then Upvalue_Arrays.Is_Released (Item.Upvalues)
       and then Local_Arrays.Is_Released (Item.Locals)
       and then Child_Arrays.Is_Released (Item.Children)
       and then Prototype_Arrays.Is_Released (Item.Prototypes));

end Pyro.Bytecode;
