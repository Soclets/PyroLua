--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  The compiler's state and its code generator, a port of PUC Lua's lcode.c.

with Pyro.Integer_Arithmetic;
with Pyro.Lexer;
with Pyro.Tokens; use Pyro.Tokens;

package body Pyro.Compiler.Code with SPARK_Mode => On is

   use type Interfaces.Integer_64;
   use type Interfaces.Unsigned_64;

   subtype Integer_64 is Interfaces.Integer_64;
   subtype Byte is Bytecode.Byte;

   --  [puc lopcodes.h:MAXARG_sJ] The largest raw sJ operand.
   Maximum_sJ : constant := Maximum_Ax;

   --  [puc lcode.c:MAXINDEXRK] The largest constant index an RK operand holds.
   Maximum_Index_RK : constant := 255;

   ---------------------------------------------------------------------------------------------
   --  Access to the state

   function Is_Released (State : Compiler_State) return Boolean
   is (Instruction_Arrays.Is_Released (State.Code)
       and then Line_Arrays.Is_Released (State.Lines)
       and then Constant_Arrays.Is_Released (State.Constants)
       and then Debug_Arrays.Is_Released (State.Debug_Locals)
       and then Child_Arrays.Is_Released (State.Children)
       and then Upvalue_Arrays.Is_Released (State.Upvalues)
       and then Variable_Arrays.Is_Released (State.Variables)
       and then Label_Arrays.Is_Released (State.Labels)
       and then Label_Arrays.Is_Released (State.Gotos)
       and then Block_Arrays.Is_Released (State.Blocks)
       and then Function_Arrays.Is_Released (State.Functions)
       and then Cache_Arrays.Is_Released (State.Cache)
       and then Token_Arrays.Is_Released (State.Tokens)
       and then Expression_Arrays.Is_Released (State.Targets)
       and then Node_Arrays.Is_Released (State.Spine));

   function Failed (State : Compiler_State) return Boolean is (State.Failed);

   function Has_Error (State : Compiler_State) return Boolean is (State.Has_Error);

   function Error_Of (State : Compiler_State) return Diagnostic is (State.Error);

   procedure Make_Internal_Error (State : in out Compiler_State) is
   begin
      State.Failed := True;
      State.Has_Error := False;
   end Make_Internal_Error;

   function Budget_Of (State : Compiler_State) return Memory_Budget is (State.Budget);

   procedure Set_Budget (State : in out Compiler_State; Budget : Memory_Budget) is
   begin
      State.Budget := Budget;
   end Set_Budget;

   function Environment_Name (State : Compiler_State) return Symbol_Index
   is (State.Environment_Name);

   function Break_Name (State : Compiler_State) return Symbol_Index is (State.Break_Name);

   function Self_Name (State : Compiler_State) return Symbol_Index is (State.Self_Name);

   function For_State_Name (State : Compiler_State) return Symbol_Index
   is (State.For_State_Name);

   procedure Set_Names
     (State : in out Compiler_State; Environment, Break, Self, For_State : Symbol_Index)
   is
   begin
      State.Environment_Name := Environment;
      State.Break_Name := Break;
      State.Self_Name := Self;
      State.For_State_Name := For_State;
   end Set_Names;

   procedure Read_Tokens
     (State : in out Compiler_State; Source : Sources.Source; Symbols : in out Symbol_Table)
   is
      Lexer   : Pyro.Lexer.Lexer_State;
      Item    : Token;
      Success : Boolean := True;
   begin
      Pyro.Lexer.Start (Lexer, Source, State.Budget);
      for Step in 0 .. Source.Length + 1 loop
         pragma Loop_Invariant (Is_Valid (Symbols));
         pragma Loop_Invariant (Pyro.Lexer.Is_Valid (Lexer, Source));
         exit when Pyro.Lexer.Failed (Lexer);
         Pyro.Lexer.Next_Token (Lexer, Source, Symbols, State.Budget, Item);
         if Natural (Item.Ordinal) /= Natural (Token_Arrays.Length (State.Tokens)) + 1
           or else Token_Arrays.Length (State.Tokens) = Work_Position'Last
         then
            Fail (State);
            exit;
         end if;
         Token_Arrays.Append
           (State.Tokens, (Kind => Item.Kind, Last => Item.Last, Line => Item.Line),
            State.Budget, Success);
         exit when not Success or else Item.Kind = End_Of_Stream;
      end loop;
      if not Success then
         Raise_Error (State, Not_Enough_Memory, 0);
      elsif Pyro.Lexer.Failed (Lexer) and then not State.Partial then
         --  A lexical error only in a chunk with errors, where the tokens before it are used.
         Fail (State);
      end if;
      Pyro.Lexer.Clear (Lexer, State.Budget);
      pragma Assert (Pyro.Lexer.Is_Released (Lexer));
   end Read_Tokens;

   function Token_Kind_At (State : Compiler_State; Ordinal : Natural) return Tokens.Token_Kind
   is (if Ordinal in 1 .. Natural (Token_Arrays.Length (State.Tokens))
       then Token_Arrays.Element (State.Tokens, Work_Position (Ordinal)).Kind
       else End_Of_Stream);

   procedure Consume (State : in out Compiler_State; Ordinal : Natural) is
      Read : constant Natural := Natural'Min (Ordinal, Bounded_Count'Last - 1);
   begin
      --  PUC Lua stops at the cut: nothing read from there on is compiled.
      if State.Partial and then State.Cut /= 0 and then Ordinal >= State.Cut then
         Fail (State);
         return;
      end if;
      if Read /= 0 and then Read = State.Lookahead_Name then
         State.Last_Token := Read + 1;
         State.Lookahead_Name := 0;
      else
         State.Last_Token := Read;
      end if;
   end Consume;

   procedure Set_Lookahead_Name (State : in out Compiler_State; Ordinal : Natural) is
   begin
      State.Lookahead_Name := Ordinal;
   end Set_Lookahead_Name;

   function Spine_Length (State : Compiler_State) return Natural
   is (Natural (Node_Arrays.Length (State.Spine)));

   function Spine_Node (State : Compiler_State; Position : Positive) return Node_Index
   is (if Position <= Natural (Node_Arrays.Length (State.Spine))
       then Node_Arrays.Element (State.Spine, Work_Position (Position)) else No_Node);

   procedure Push_Node (State : in out Compiler_State; Node : Node_Index; Success : out Boolean)
   is
   begin
      Node_Arrays.Append (State.Spine, Node, State.Budget, Success);
   end Push_Node;

   procedure Truncate_Spine (State : in out Compiler_State; Length : Natural) is
   begin
      if Length <= Natural (Node_Arrays.Length (State.Spine)) then
         Node_Arrays.Truncate (State.Spine, Node_Arrays.Extended_Index (Length));
      end if;
   end Truncate_Spine;

   function Targets_Length (State : Compiler_State) return Natural
   is (Natural (Expression_Arrays.Length (State.Targets)));

   function Target_At (State : Compiler_State; Position : Positive) return Expression
   is (if Position <= Natural (Expression_Arrays.Length (State.Targets))
       then Expression_Arrays.Element (State.Targets, Work_Position (Position))
       else (others => <>));

   procedure Set_Target (State : in out Compiler_State; Position : Positive; Item : Expression)
   is
   begin
      if Position <= Natural (Expression_Arrays.Length (State.Targets)) then
         Expression_Arrays.Replace_Element (State.Targets, Work_Position (Position), Item);
      else
         Fail (State);
      end if;
   end Set_Target;

   procedure Push_Target (State : in out Compiler_State; Item : Expression; Success : out Boolean)
   is
   begin
      Expression_Arrays.Append (State.Targets, Item, State.Budget, Success);
   end Push_Target;

   procedure Truncate_Targets (State : in out Compiler_State; Length : Natural) is
   begin
      if Length <= Natural (Expression_Arrays.Length (State.Targets)) then
         Expression_Arrays.Truncate
           (State.Targets, Expression_Arrays.Extended_Index (Length));
      end if;
   end Truncate_Targets;

   function Child_Count (State : Compiler_State) return Natural
   is (if Natural (Child_Arrays.Length (State.Children)) >= Current (State).Child_Base
       then Natural (Child_Arrays.Length (State.Children)) - Current (State).Child_Base
       else 0);

   procedure Set_Environment_Upvalue (State : in out Compiler_State) is
      Item : Function_Entry;
   begin
      if Upvalue_Arrays.Length (State.Upvalues) >= 1 then
         Upvalue_Arrays.Replace_Element
           (State.Upvalues, 1,
            (Name => State.Environment_Name, In_Stack => True, Index => 0,
             Kind => Regular_Variable));
         Item := Current (State);
         Item.Upvalue_Count := 1;
         Set_Current (State, Item);
      else
         Fail (State);
      end if;
   end Set_Environment_Upvalue;

   procedure Release (State : in out Compiler_State) is
   begin
      Instruction_Arrays.Clear (State.Code, State.Budget);
      Line_Arrays.Clear (State.Lines, State.Budget);
      Constant_Arrays.Clear (State.Constants, State.Budget);
      Debug_Arrays.Clear (State.Debug_Locals, State.Budget);
      Child_Arrays.Clear (State.Children, State.Budget);
      Upvalue_Arrays.Clear (State.Upvalues, State.Budget);
      Variable_Arrays.Clear (State.Variables, State.Budget);
      Label_Arrays.Clear (State.Labels, State.Budget);
      Label_Arrays.Clear (State.Gotos, State.Budget);
      Block_Arrays.Clear (State.Blocks, State.Budget);
      Function_Arrays.Clear (State.Functions, State.Budget);
      Cache_Arrays.Clear (State.Cache, State.Budget);
      Token_Arrays.Clear (State.Tokens, State.Budget);
      Expression_Arrays.Clear (State.Targets, State.Budget);
      Node_Arrays.Clear (State.Spine, State.Budget);
   end Release;

   ---------------------------------------------------------------------------------------------
   --  State

   procedure Fail (State : in out Compiler_State) is
   begin
      State.Failed := True;
   end Fail;

   procedure Set_Partial (State : in out Compiler_State; Cut : Natural) is
   begin
      State.Partial := True;
      State.Cut := Cut;
   end Set_Partial;

   function Is_Partial (State : Compiler_State) return Boolean is (State.Partial);

   function Token_Line (State : Compiler_State; Ordinal : Natural) return Line_Number is
     (if Ordinal = 0 then 1
      elsif Ordinal <= Natural (Token_Arrays.Length (State.Tokens))
      then Token_Arrays.Element (State.Tokens, Work_Position (Ordinal)).Line
      elsif Token_Arrays.Length (State.Tokens) > 0
      then Token_Arrays.Element (State.Tokens, Token_Arrays.Length (State.Tokens)).Line
      else 1);

   function Last_Line (State : Compiler_State) return Line_Number
   is (Token_Line (State, State.Last_Token));

   function Token_At (State : Compiler_State; Position : Span_End) return Natural is
      Low  : Natural := 1;
      High : Natural := Natural (Token_Arrays.Length (State.Tokens));
      Middle : Natural;
   begin
      --  The first token whose last byte is at or after Position.
      while Low < High loop
         pragma Loop_Variant (Decreases => High - Low);
         pragma Loop_Invariant (Low in 1 .. High);
         pragma Loop_Invariant (High <= Natural (Token_Arrays.Length (State.Tokens)));
         Middle := Low + (High - Low) / 2;
         if Token_Arrays.Element (State.Tokens, Work_Position (Middle)).Last < Position then
            Low := Middle + 1;
         else
            High := Middle;
         end if;
      end loop;
      return Low;
   end Token_At;

   procedure Raise_Error (State : in out Compiler_State; What : Problem; Function_Line : Natural)
   is
      Current_Token : constant Natural := State.Last_Token + 1;
   begin
      if State.Failed then
         return;
      end if;
      State.Failed := True;
      State.Has_Error := True;
      State.Error :=
        (What         => What,
         Has_Lua_Line => True,
         Lua_Line     => Token_Line (State, Current_Token),
         Other_Line   =>
           (if Function_Line in 1 .. Natural (Line_Number'Last)
            then Line_Number (Function_Line) else 1),
         In_Main_Function => Function_Line = 0,
         Detection    =>
           (Ordinal => Token_Ordinal (Current_Token),
            --  Raised while the token is read, before the parser looks at it.
            During  => Resolving),
         others       => <>);
   end Raise_Error;

   function Current (State : Compiler_State) return Function_Entry
   is (if Function_Arrays.Length (State.Functions) > 0
       then Function_Arrays.Element (State.Functions, Function_Arrays.Length (State.Functions))
       else (others => <>));

   procedure Set_Current (State : in out Compiler_State; Item : Function_Entry) is
   begin
      if Function_Arrays.Length (State.Functions) > 0 then
         Function_Arrays.Replace_Element
           (State.Functions, Function_Arrays.Length (State.Functions), Item);
      else
         Fail (State);
      end if;
   end Set_Current;

   function PC (State : Compiler_State) return Natural
   is (if Natural (Instruction_Arrays.Length (State.Code)) >= Current (State).Code_Base
       then Natural (Instruction_Arrays.Length (State.Code)) - Current (State).Code_Base
       else 0);

   --  The position of instruction Index of the open function, or 0 when there is none.
   function Code_Position (State : Compiler_State; Index : Natural) return Natural
   is (if Index < PC (State)
          and then Current (State).Code_Base + Index + 1
                     <= Natural (Instruction_Arrays.Length (State.Code))
       then Current (State).Code_Base + Index + 1
       else 0);

   function Get (State : Compiler_State; Index : Natural) return Instruction
   is (if Code_Position (State, Index) /= 0
       then Instruction_Arrays.Element (State.Code, Work_Position (Code_Position (State, Index)))
       else (others => <>));

   procedure Put (State : in out Compiler_State; Index : Natural; Item : Instruction) is
      Position : constant Natural := Code_Position (State, Index);
   begin
      if Position /= 0 then
         Instruction_Arrays.Replace_Element (State.Code, Work_Position (Position), Item);
      else
         Fail (State);
      end if;
   end Put;

   function Variable (State : Compiler_State; Index : Natural) return Variable_Entry
   is (if Index < Natural (Variable_Arrays.Length (State.Variables))
       then Variable_Arrays.Element (State.Variables, Work_Position (Index + 1))
       else (others => <>));

   function Local_Variable_Of (State : Compiler_State; Index : Natural) return Variable_Entry
   is (if Index <= Natural'Last - Current (State).First_Local
       then Variable (State, Current (State).First_Local + Index)
       else (others => <>));

   function Register_Level (State : Compiler_State; Count : Natural) return Natural is
   begin
      for Index in reverse 0 .. Count - 1 loop
         if Local_Variable_Of (State, Index).Kind /= Compile_Time_Variable then
            return Natural'Min (Local_Variable_Of (State, Index).Register, 255) + 1;
         end if;
      end loop;
      return 0;
   end Register_Level;

   function Variables_On_Stack (State : Compiler_State) return Natural
   is (Register_Level (State, Current (State).Active));

   ---------------------------------------------------------------------------------------------
   --  Emitting instructions

   --  [puc lcode.c:luaK_code] Appends Item with the line of the token read last.
   procedure Emit (State : in out Compiler_State; Item : Instruction; Result : out Natural) is
      Success : Boolean;
   begin
      Result := PC (State);
      if Instruction_Arrays.Length (State.Code) = Work_Position'Last
        or else Natural (Line_Arrays.Length (State.Lines))
                  /= Natural (Instruction_Arrays.Length (State.Code))
        or else PC (State) >= Entry_Number'Last
      then
         Fail (State);
         return;
      end if;
      Instruction_Arrays.Append (State.Code, Item, State.Budget, Success);
      if Success then
         Line_Arrays.Append (State.Lines, Last_Line (State), State.Budget, Success);
      end if;
      if not Success then
         Raise_Error (State, Not_Enough_Memory, 0);
      end if;
   end Emit;

   procedure Code_Raw (State : in out Compiler_State; Item : Instruction) is
      Ignored : Natural;
   begin
      Emit (State, Item, Ignored);
   end Code_Raw;

   procedure Code_ABC
     (State : in out Compiler_State;
      Operation : Opcode;
      A, B, C : Natural;
      K : Boolean;
      Result : out Natural)
   is
   begin
      if A > 255 or else B > 255 or else C > 255 then
         Fail (State);
         Result := 0;
         return;
      end if;
      Emit (State, (Operation => Operation, A => Byte (A), B => Byte (B), C => Byte (C),
                    K => K, Wide => 0), Result);
   end Code_ABC;

   procedure Code_ABx
     (State : in out Compiler_State; Operation : Opcode; A, Bx : Natural; Result : out Natural)
   is
   begin
      if A > 255 or else Bx > Maximum_Bx then
         Fail (State);
         Result := 0;
         return;
      end if;
      Emit (State, (Operation => Operation, A => Byte (A), Wide => Wide_Argument (Bx),
                    others => <>), Result);
   end Code_ABx;

   --  [puc lcode.c:codeAsBx].
   procedure Code_AsBx
     (State : in out Compiler_State; Operation : Opcode; A : Natural; Value : Integer)
   is
      Ignored : Natural;
   begin
      if A > 255 or else Value not in -Offset_sBx .. Maximum_Bx - Offset_sBx then
         Fail (State);
         return;
      end if;
      Emit (State, (Operation => Operation, A => Byte (A),
                    Wide => Wide_Argument (Value + Offset_sBx), others => <>), Ignored);
   end Code_AsBx;

   --  [puc lcode.c:codesJ].
   procedure Code_sJ (State : in out Compiler_State; Offset : Integer; Result : out Natural) is
   begin
      if Offset not in -Offset_sJ .. Maximum_sJ - Offset_sJ then
         Fail (State);
         Result := 0;
         return;
      end if;
      Emit (State, (Operation => Jump, Wide => Wide_Argument (Offset + Offset_sJ),
                    others => <>), Result);
   end Code_sJ;

   --  [puc lcode.c:codeextraarg].
   procedure Code_Extra_Argument (State : in out Compiler_State; Value : Natural) is
      Ignored : Natural;
   begin
      if Value > Maximum_Ax then
         Fail (State);
         return;
      end if;
      Emit (State, (Operation => Extra_Argument, Wide => Wide_Argument (Value),
                    others => <>), Ignored);
   end Code_Extra_Argument;

   procedure Fix_Line (State : in out Compiler_State; Line : Line_Number) is
   begin
      if Line_Arrays.Length (State.Lines) > 0 and then PC (State) > 0 then
         Line_Arrays.Replace_Element (State.Lines, Line_Arrays.Length (State.Lines), Line);
      else
         Fail (State);
      end if;
   end Fix_Line;

   --  [puc lcode.c:removelastinstruction].
   procedure Remove_Last_Instruction (State : in out Compiler_State) is
   begin
      if PC (State) > 0
        and then Line_Arrays.Length (State.Lines) = Instruction_Arrays.Length (State.Code)
      then
         Instruction_Arrays.Truncate (State.Code, Instruction_Arrays.Length (State.Code) - 1);
         Line_Arrays.Truncate (State.Lines, Line_Arrays.Length (State.Lines) - 1);
      else
         Fail (State);
      end if;
   end Remove_Last_Instruction;

   --  [puc lcode.c:luaK_codek].
   procedure Code_Constant (State : in out Compiler_State; Register, Index : Natural) is
      Ignored : Natural;
   begin
      if Index <= Maximum_Bx then
         Code_ABx (State, Load_Constant, Register, Index, Ignored);
      else
         Code_ABx (State, Load_Constant_Extra, Register, 0, Ignored);
         Code_Extra_Argument (State, Index);
      end if;
   end Code_Constant;

   procedure Check_Stack (State : in out Compiler_State; Count : Natural) is
      Item      : Function_Entry := Current (State);
      New_Stack : Natural;
   begin
      if Count > Maximum_Registers or else Item.Free_Register > Maximum_Registers then
         Raise_Error (State, Too_Many_Registers, 0);
         return;
      end if;
      New_Stack := Item.Free_Register + Count;
      if New_Stack > Natural (Item.Facts.Stack_Size) then
         if New_Stack >= Maximum_Registers then
            Raise_Error (State, Too_Many_Registers, 0);
            return;
         end if;
         Item.Facts.Stack_Size := Byte (New_Stack);
         Set_Current (State, Item);
      end if;
   end Check_Stack;

   procedure Reserve_Registers (State : in out Compiler_State; Count : Natural) is
      Item : Function_Entry;
   begin
      Check_Stack (State, Count);
      if State.Failed then
         return;
      end if;
      Item := Current (State);
      if Item.Free_Register > Maximum_Registers or else Count > Maximum_Registers then
         Fail (State);
         return;
      end if;
      Item.Free_Register := Item.Free_Register + Count;
      Set_Current (State, Item);
   end Reserve_Registers;

   --  [puc lcode.c:freereg].
   procedure Free_Register (State : in out Compiler_State; Register : Natural) is
      Item : Function_Entry := Current (State);
   begin
      if Register >= Variables_On_Stack (State) then
         if Item.Free_Register = 0 then
            Fail (State);
            return;
         end if;
         Item.Free_Register := Item.Free_Register - 1;
         Set_Current (State, Item);
      end if;
   end Free_Register;

   --  [puc lcode.c:freeregs].
   procedure Free_Registers (State : in out Compiler_State; First, Second : Integer) is
   begin
      if First > Second then
         if First >= 0 then
            Free_Register (State, First);
         end if;
         if Second >= 0 then
            Free_Register (State, Second);
         end if;
      else
         if Second >= 0 then
            Free_Register (State, Second);
         end if;
         if First >= 0 then
            Free_Register (State, First);
         end if;
      end if;
   end Free_Registers;

   --  [puc lcode.c:freeexp].
   procedure Free_Expression (State : in out Compiler_State; Item : Expression) is
   begin
      if Item.Kind = Fixed_Register then
         Free_Register (State, Item.Info);
      end if;
   end Free_Expression;

   --  [puc lcode.c:freeexps].
   procedure Free_Expressions (State : in out Compiler_State; Left, Right : Expression) is
   begin
      Free_Registers
        (State,
         (if Left.Kind = Fixed_Register then Integer (Natural'Min (Left.Info, 255)) else -1),
         (if Right.Kind = Fixed_Register then Integer (Natural'Min (Right.Info, 255)) else -1));
   end Free_Expressions;

   ---------------------------------------------------------------------------------------------
   --  Constants

   --  The cache key of a constant used as a Lua table key: an integral float is an integer.
   procedure Key_Of
     (Value : Constant_Value; Kind : out Key_Kind; Bits : out Interfaces.Unsigned_64)
   is
      Integral : Integer_64;
      Success  : Boolean;
   begin
      Bits := 0;
      case Value.Kind is
         when Nil_Constant => Kind := Nil_Key;
         when False_Constant => Kind := False_Key;
         when True_Constant => Kind := True_Key;
         when Integer_Constant =>
            Kind := Integer_Key;
            Bits := Value.Bits;
         when Float_Constant =>
            Floats.To_Integer (Value.Bits, Integral, Success);
            if Success then
               Kind := Integer_Key;
               Bits := Integer_Arithmetic.To_Unsigned (Integral);
            else
               Kind := Float_Key;
               Bits := Value.Bits;
            end if;
         when Short_String_Constant | Long_String_Constant =>
            Kind := String_Key;
      end case;
   end Key_Of;

   --  The slot of the cache where a key is or would go.
   function Hash (Kind : Key_Kind; Bits : Interfaces.Unsigned_64; Symbol : Symbol_Index;
                  Capacity : Positive) return Natural
   with Post => Hash'Result < Capacity;

   function Hash (Kind : Key_Kind; Bits : Interfaces.Unsigned_64; Symbol : Symbol_Index;
                  Capacity : Positive) return Natural
   is
      Mixed : constant Interfaces.Unsigned_64 :=
        ((Bits xor Interfaces.Unsigned_64 (Symbol) * 16#9E37_79B9#
          xor Interfaces.Unsigned_64 (Key_Kind'Pos (Kind)))
         * 16#9E37_79B9_7F4A_7C15#) / 2 ** 32;
      Small : constant Natural := Natural (Mixed mod 2 ** 30);
   begin
      return Small mod Capacity;
   end Hash;

   --  Looks Key up in the cache: Slot is its slot (0 when the cache is full or empty), Found
   --  whether it holds the key.
   procedure Find
     (State  : Compiler_State;
      Kind   : Key_Kind;
      Bits   : Interfaces.Unsigned_64;
      Symbol : Symbol_Index;
      Slot   : out Natural;
      Found  : out Boolean)
   with
     Post =>
       Slot <= Natural (Cache_Arrays.Length (State.Cache))
       and then (if Found then Slot >= 1)
   is
      Capacity : constant Natural := Natural (Cache_Arrays.Length (State.Cache));
      Probe    : Natural;
      Item     : Cache_Entry;
   begin
      Slot := 0;
      Found := False;
      if Capacity = 0 then
         return;
      end if;
      Probe := Hash (Kind, Bits, Symbol, Capacity);
      for Step in 1 .. Capacity loop
         pragma Loop_Invariant (Probe < Capacity);
         Item := Cache_Arrays.Element (State.Cache, Work_Position (Probe + 1));
         if not Item.Used then
            Slot := Probe + 1;
            return;
         elsif Item.Kind = Kind and then Item.Bits = Bits and then Item.Symbol = Symbol then
            Slot := Probe + 1;
            Found := True;
            return;
         end if;
         Probe := (if Probe + 1 = Capacity then 0 else Probe + 1);
      end loop;
   end Find;

   --  Doubles the cache (or makes its first slots), keeping its entries.
   procedure Grow_Cache (State : in out Compiler_State) is
      Old_Capacity : constant Natural := Natural (Cache_Arrays.Length (State.Cache));
      New_Capacity : constant Natural := (if Old_Capacity = 0 then 64 else 2 * Old_Capacity);
      Old_Cache    : Cache_Arrays.Growable_Array;
      Item         : Cache_Entry;
      Slot         : Natural;
      Found        : Boolean;
      Success      : Boolean := True;
   begin
      if Old_Capacity >= 2 ** 26 then
         Raise_Error (State, Not_Enough_Memory, 0);
         return;
      end if;
      Cache_Arrays.Swap (State.Cache, Old_Cache);
      for Count in 1 .. New_Capacity loop
         pragma Loop_Invariant (Natural (Cache_Arrays.Length (State.Cache)) = Count - 1);
         Cache_Arrays.Append (State.Cache, (others => <>), State.Budget, Success);
         exit when not Success;
      end loop;
      if Success then
         for Position in 1 .. Cache_Arrays.Length (Old_Cache) loop
            Item := Cache_Arrays.Element (Old_Cache, Position);
            if Item.Used then
               Find (State, Item.Kind, Item.Bits, Item.Symbol, Slot, Found);
               if not Found and then Slot in 1 .. Natural (Cache_Arrays.Length (State.Cache))
               then
                  Cache_Arrays.Replace_Element (State.Cache, Work_Position (Slot), Item);
               end if;
            end if;
         end loop;
      else
         Raise_Error (State, Not_Enough_Memory, 0);
      end if;
      Cache_Arrays.Clear (Old_Cache, State.Budget);
      pragma Assert (Cache_Arrays.Is_Released (Old_Cache));
   end Grow_Cache;

   --  Constant Index of the open function (a nil if there is none).
   function Constant_Of (State : Compiler_State; Index : Natural) return Constant_Value
   is (if Index <= Natural'Last - Current (State).Constant_Base - 1
          and then Current (State).Constant_Base + Index
                     < Natural (Constant_Arrays.Length (State.Constants))
       then Constant_Arrays.Element
              (State.Constants, Work_Position (Current (State).Constant_Base + Index + 1))
       else (others => <>));

   --  The number of constants of the open function.
   function Constant_Count (State : Compiler_State) return Natural
   is (if Natural (Constant_Arrays.Length (State.Constants)) >= Current (State).Constant_Base
       then Natural (Constant_Arrays.Length (State.Constants)) - Current (State).Constant_Base
       else 0);

   --  [puc lvm.c:luaV_rawequalobj] with the same type tag: Left and Right are the same value.
   function Same_Value (Left, Right : Constant_Value) return Boolean
   is (Left.Kind = Right.Kind
       and then (case Left.Kind is
                   when Nil_Constant | False_Constant | True_Constant => True,
                   when Integer_Constant => Left.Bits = Right.Bits,
                   when Float_Constant =>
                     Left.Bits = Right.Bits
                     or else (Floats.Is_Zero (Left.Bits) and then Floats.Is_Zero (Right.Bits)),
                   when Short_String_Constant | Long_String_Constant =>
                     Left.Symbol = Right.Symbol));

   --  [puc lcode.c:addk] The index of Value in the open function's constants, with Key the
   --  scanner-table key PUC Lua looks it up with.
   procedure Add_Constant
     (State : in out Compiler_State;
      Key   : Constant_Value;
      Value : Constant_Value;
      Index : out Natural)
   is
      Kind    : Key_Kind;
      Bits    : Interfaces.Unsigned_64;
      Symbol  : constant Symbol_Index :=
        (if Key.Kind in String_Constant_Kind then Key.Symbol else No_Symbol);
      Slot    : Natural;
      Found   : Boolean;
      Success : Boolean;
   begin
      Index := 0;
      if State.Failed then
         return;
      end if;
      Key_Of (Key, Kind, Bits);
      Find (State, Kind, Bits, Symbol, Slot, Found);
      if Found then
         declare
            Cached : constant Natural :=
              Cache_Arrays.Element (State.Cache, Work_Position (Slot)).Index;
         begin
            if Cached < Constant_Count (State)
              and then Same_Value (Constant_Of (State, Cached), Value)
            then
               Index := Cached;
               return;
            end if;
         end;
      elsif State.Cache_Used >= 2 ** 26 then
         Raise_Error (State, Not_Enough_Memory, 0);
         return;
      elsif Slot = 0
        or else 2 * (State.Cache_Used + 1) > Natural (Cache_Arrays.Length (State.Cache))
      then
         Grow_Cache (State);
         if State.Failed then
            return;
         end if;
         Find (State, Kind, Bits, Symbol, Slot, Found);
      end if;
      Index := Constant_Count (State);
      if Slot not in 1 .. Natural (Cache_Arrays.Length (State.Cache))
        or else Index >= Maximum_Ax
        or else Constant_Arrays.Length (State.Constants) = Work_Position'Last
      then
         Fail (State);
         return;
      end if;
      if not Found and then State.Cache_Used < 2 ** 26 then
         State.Cache_Used := State.Cache_Used + 1;
      end if;
      Cache_Arrays.Replace_Element
        (State.Cache, Work_Position (Slot),
         (Used => True, Kind => Kind, Bits => Bits, Symbol => Symbol, Index => Index));
      Constant_Arrays.Append (State.Constants, Value, State.Budget, Success);
      if not Success then
         Raise_Error (State, Not_Enough_Memory, 0);
      end if;
   end Add_Constant;

   --  The constant for a string.
   function String_Constant (Symbol : Symbol_Index; Short : Boolean) return Constant_Value
   is ((Kind => (if Short then Short_String_Constant else Long_String_Constant),
        Symbol => Symbol, Bits => 0));

   --  [puc lcode.c:stringK].
   procedure String_K
     (State : in out Compiler_State; Symbol : Symbol_Index; Short : Boolean; Index : out Natural)
   is
   begin
      Add_Constant (State, String_Constant (Symbol, Short), String_Constant (Symbol, Short),
                    Index);
   end String_K;

   --  [puc lcode.c:luaK_intK].
   procedure Integer_K (State : in out Compiler_State; Value : Integer_64; Index : out Natural)
   is
      Item : constant Constant_Value :=
        (Kind => Integer_Constant, Bits => Integer_Arithmetic.To_Unsigned (Value), others => <>);
   begin
      Add_Constant (State, Item, Item, Index);
   end Integer_K;

   --  [puc lcode.c:luaK_numberK].
   procedure Number_K
     (State : in out Compiler_State; Value : Floats.Float_Bits; Index : out Natural)
   is
      --  2^-52, ldexp (1.0, -nbm + 1) with 53 mantissa bits.
      Epsilon  : constant Floats.Float_Bits := 16#3CB0_0000_0000_0000#;
      Item     : constant Constant_Value := (Kind => Float_Constant, Bits => Value, others => <>);
      Integral : Integer_64;
      Success  : Boolean;
      Key      : Floats.Float_Bits;
   begin
      Floats.To_Integer (Value, Integral, Success);
      if not Success then
         Add_Constant (State, Item, Item, Index);
      else
         Key := (if Integral = 0 then Epsilon
                 else Floats.Arithmetic
                        (Floats.Add, Value,
                         Floats.Arithmetic (Floats.Multiply, Value, Epsilon)));
         Add_Constant (State, (Kind => Float_Constant, Bits => Key, others => <>), Item, Index);
      end if;
   end Number_K;

   --  [puc lcode.c:boolF, boolT, nilK].
   procedure Simple_K (State : in out Compiler_State; Kind : Constant_Kind; Index : out Natural)
   is
   begin
      Add_Constant (State, (Kind => Kind, others => <>), (Kind => Kind, others => <>), Index);
   end Simple_K;

   --  [puc lcode.c:fitsC].
   function Fits_C (Value : Integer_64) return Boolean
   is (Value in -Offset_sC .. Maximum_C - Offset_sC);

   --  The excess-127 operand for an immediate that fits C.
   function Excess (Value : Integer_64) return Natural
   is (Natural (Value + Offset_sC))
   with Pre => Fits_C (Value), Post => Excess'Result <= Maximum_C;

   --  [puc lcode.c:fitsBx].
   function Fits_Bx (Value : Integer_64) return Boolean
   is (Value in -Offset_sBx .. Maximum_Bx - Offset_sBx);

   procedure Load_Integer (State : in out Compiler_State; Register : Natural;
                           Value : Integer_64)
   is
      Index : Natural;
   begin
      if Fits_Bx (Value) then
         Code_AsBx (State, Load_Integer, Register, Integer (Value));
      else
         Integer_K (State, Value, Index);
         Code_Constant (State, Register, Index);
      end if;
   end Load_Integer;

   --  [puc lcode.c:luaK_float].
   procedure Load_Float
     (State : in out Compiler_State; Register : Natural; Value : Floats.Float_Bits)
   is
      Integral : Integer_64;
      Success  : Boolean;
      Index    : Natural;
   begin
      Floats.To_Integer (Value, Integral, Success);
      if Success and then Fits_Bx (Integral) then
         Code_AsBx (State, Load_Float, Register, Integer (Integral));
      else
         Number_K (State, Value, Index);
         Code_Constant (State, Register, Index);
      end if;
   end Load_Float;

   ---------------------------------------------------------------------------------------------
   --  Jumps

   --  [puc lcode.c:previousinstruction] The instruction before, if it is not a jump target.
   procedure Previous_Instruction
     (State : Compiler_State; Item : out Instruction; Exists : out Boolean)
   is
   begin
      Exists := PC (State) > Current (State).Last_Target and then PC (State) > 0;
      Item := (if Exists then Get (State, PC (State) - 1) else (others => <>));
   end Previous_Instruction;

   procedure Load_Nil (State : in out Compiler_State; From, Count : Natural) is
      First    : Natural := From;
      Last     : Natural;
      Previous : Instruction;
      Exists   : Boolean;
      Ignored  : Natural;
   begin
      if Count = 0 or else From > 255 or else Count > 256 then
         Fail (State);
         return;
      end if;
      Last := From + Count - 1;
      Previous_Instruction (State, Previous, Exists);
      if Exists and then Previous.Operation = Load_Nil then
         declare
            Previous_First : constant Natural := Natural (Previous.A);
            Previous_Last  : constant Natural := Previous_First + Natural (Previous.B);
         begin
            if (Previous_First <= First and then First <= Previous_Last + 1)
              or else (First <= Previous_First and then Previous_First <= Last + 1)
            then
               First := Natural'Min (First, Previous_First);
               Last := Natural'Max (Last, Previous_Last);
               if Last - First > 255 then
                  Fail (State);
                  return;
               end if;
               Previous.A := Byte (First);
               Previous.B := Byte (Last - First);
               if PC (State) = 0 then
                  Fail (State);
                  return;
               end if;
               Put (State, PC (State) - 1, Previous);
               return;
            end if;
         end;
      end if;
      Code_ABC (State, Load_Nil, From, Count - 1, 0, False, Ignored);
   end Load_Nil;

   --  [puc lcode.c:getjump].
   function Next_Jump (State : Compiler_State; Position : Natural) return Jump_List is
      Offset : constant Integer := Integer (Get (State, Position).Wide) - Offset_sJ;
   begin
      if Offset = No_Jump or else Position >= Entry_Number'Last
        or else Position + 1 + Offset not in 0 .. Entry_Number'Last
      then
         return No_Jump;
      end if;
      return Position + 1 + Offset;
   end Next_Jump;

   --  [puc lcode.c:fixjump].
   procedure Fix_Jump (State : in out Compiler_State; Position, Target : Natural) is
      Item   : Instruction := Get (State, Position);
      Offset : Integer;
   begin
      if Position >= Entry_Number'Last or else Position >= PC (State)
        or else Target > Entry_Number'Last
      then
         Fail (State);
         return;
      end if;
      Offset := Target - (Position + 1);
      if Offset not in -Offset_sJ .. Maximum_sJ - Offset_sJ then
         Raise_Error (State, Control_Structure_Too_Long, 0);
         return;
      end if;
      if Item.Operation /= Jump then
         Fail (State);
         return;
      end if;
      Item.Wide := Wide_Argument (Offset + Offset_sJ);
      Put (State, Position, Item);
   end Fix_Jump;

   procedure Concatenate_Jumps (State : in out Compiler_State; List : in out Jump_List;
                                Other : Jump_List)
   is
      Last : Jump_List;
      Next : Jump_List;
   begin
      if Other = No_Jump then
         return;
      elsif List = No_Jump then
         List := Other;
      else
         Last := List;
         --  A jump list has at most one entry per instruction.
         for Step in 0 .. PC (State) loop
            pragma Loop_Invariant (Last >= 0);
            Next := Next_Jump (State, Last);
            if Next = No_Jump then
               Fix_Jump (State, Last, Other);
               return;
            end if;
            Last := Next;
         end loop;
         Fail (State);
      end if;
   end Concatenate_Jumps;

   procedure Jump (State : in out Compiler_State; Result : out Jump_List) is
      Position : Natural;
   begin
      Code_sJ (State, No_Jump, Position);
      Result := (if Position <= Entry_Number'Last then Position else No_Jump);
   end Jump;

   procedure Return_Values (State : in out Compiler_State; First : Natural; Count : Integer) is
      Ignored : Natural;
   begin
      if Count < -1 or else Count > 254 then
         Fail (State);
         return;
      end if;
      Code_ABC (State,
                (case Count is
                   when 0 => Return_None,
                   when 1 => Return_One,
                   when others => Bytecode.Return_Values),
                First, Count + 1, 0, False, Ignored);
   end Return_Values;

   --  [puc lcode.c:condjump].
   procedure Conditional_Jump
     (State : in out Compiler_State;
      Operation : Opcode;
      A, B, C : Natural;
      K : Boolean;
      Result : out Jump_List)
   is
      Ignored : Natural;
   begin
      Code_ABC (State, Operation, A, B, C, K, Ignored);
      Jump (State, Result);
   end Conditional_Jump;

   procedure Get_Label (State : in out Compiler_State; Result : out Natural) is
      Item : Function_Entry := Current (State);
   begin
      Result := PC (State);
      Item.Last_Target := Result;
      Set_Current (State, Item);
   end Get_Label;

   --  [puc lcode.c:getjumpcontrol] The instruction controlling the jump at Position.
   function Jump_Control (State : Compiler_State; Position : Natural) return Natural
   is (if Position >= 1 and then Get (State, Position - 1).Operation in Test_Opcode
       then Position - 1 else Position);

   --  [puc lcode.c:patchtestreg].
   procedure Patch_Test_Register
     (State : in out Compiler_State; Node : Natural; Register : Natural; Patched : out Boolean)
   is
      Control : constant Natural := Jump_Control (State, Node);
      Item    : Instruction := Get (State, Control);
   begin
      if Item.Operation /= Test_Set then
         Patched := False;
         return;
      end if;
      Patched := True;
      if Register /= No_Register and then Register /= Natural (Item.B) then
         if Register > 255 then
            Fail (State);
            return;
         end if;
         Item.A := Byte (Register);
      else
         Item := (Operation => Test, A => Item.B, B => 0, C => 0, K => Item.K, Wide => 0);
      end if;
      Put (State, Control, Item);
   end Patch_Test_Register;

   --  [puc lcode.c:removevalues].
   procedure Remove_Values (State : in out Compiler_State; List : Jump_List) is
      Position : Jump_List := List;
      Ignored  : Boolean;
   begin
      for Step in 0 .. PC (State) loop
         exit when Position = No_Jump;
         Patch_Test_Register (State, Position, No_Register, Ignored);
         Position := Next_Jump (State, Position);
      end loop;
      if Position /= No_Jump then
         Fail (State);
      end if;
   end Remove_Values;

   --  [puc lcode.c:patchlistaux].
   procedure Patch_List_Auxiliary
     (State : in out Compiler_State;
      List : Jump_List;
      Value_Target : Natural;
      Register : Natural;
      Default_Target : Natural)
   is
      Position : Jump_List := List;
      Next     : Jump_List;
      Patched  : Boolean;
   begin
      for Step in 0 .. PC (State) loop
         exit when Position = No_Jump or else State.Failed;
         Next := Next_Jump (State, Position);
         Patch_Test_Register (State, Position, Register, Patched);
         Fix_Jump (State, Position, (if Patched then Value_Target else Default_Target));
         Position := Next;
      end loop;
      if Position /= No_Jump and then not State.Failed then
         Fail (State);
      end if;
   end Patch_List_Auxiliary;

   procedure Patch_List (State : in out Compiler_State; List : Jump_List; Target : Natural) is
   begin
      Patch_List_Auxiliary (State, List, Target, No_Register, Target);
   end Patch_List;

   procedure Patch_To_Here (State : in out Compiler_State; List : Jump_List) is
      Here : Natural;
   begin
      Get_Label (State, Here);
      Patch_List (State, List, Here);
   end Patch_To_Here;

   ---------------------------------------------------------------------------------------------
   --  Expressions

   --  [puc lcode.c:const2exp].
   procedure Constant_To_Expression (Value : Constant_Value; Item : in out Expression) is
   begin
      case Value.Kind is
         when Integer_Constant =>
            Item.Kind := Integer_Value;
            Item.Integer_Bits := Integer_Arithmetic.To_Signed (Value.Bits);
         when Float_Constant =>
            Item.Kind := Float_Value;
            Item.Float_Bits := Value.Bits;
         when False_Constant => Item.Kind := False_Value;
         when True_Constant => Item.Kind := True_Value;
         when Nil_Constant => Item.Kind := Nil_Value;
         when Short_String_Constant | Long_String_Constant =>
            Item.Kind := String_Value;
            Item.String_Symbol := Value.Symbol;
            Item.String_Short := Value.Kind = Short_String_Constant;
      end case;
   end Constant_To_Expression;

   procedure To_Constant
     (State : Compiler_State; Item : Expression; Value : out Constant_Value;
      Success : out Boolean)
   is
   begin
      Value := (others => <>);
      Success := not Has_Jumps (Item);
      if not Success then
         return;
      end if;
      case Item.Kind is
         when False_Value => Value.Kind := False_Constant;
         when True_Value => Value.Kind := True_Constant;
         when Nil_Value => Value.Kind := Nil_Constant;
         when String_Value => Value := String_Constant (Item.String_Symbol, Item.String_Short);
         when Compile_Time_Constant => Value := Variable (State, Item.Info).Value;
         when Integer_Value =>
            Value := (Kind => Integer_Constant,
                      Bits => Integer_Arithmetic.To_Unsigned (Item.Integer_Bits), others => <>);
         when Float_Value =>
            Value := (Kind => Float_Constant, Bits => Item.Float_Bits, others => <>);
         when others => Success := False;
      end case;
   end To_Constant;

   procedure Set_Returns (State : in out Compiler_State; Item : Expression; Count : Integer) is
      Instruction_Item : Instruction := Get (State, Item.Info);
      Free             : constant Natural := Current (State).Free_Register;
   begin
      if Count not in -1 .. 254 then
         Fail (State);
         return;
      end if;
      Instruction_Item.C := Byte (Count + 1);
      if Item.Kind = Open_Call then
         Put (State, Item.Info, Instruction_Item);
      else
         if Free > 255 then
            Fail (State);
            return;
         end if;
         Instruction_Item.A := Byte (Free);
         Put (State, Item.Info, Instruction_Item);
         Reserve_Registers (State, 1);
      end if;
   end Set_Returns;

   --  [puc lcode.c:str2K].
   procedure String_To_Constant (State : in out Compiler_State; Item : in out Expression) is
      Index : Natural;
   begin
      String_K (State, Item.String_Symbol, Item.String_Short, Index);
      Item.Info := Index;
      Item.Kind := Constant_Index;
   end String_To_Constant;

   procedure Set_One_Return (State : in out Compiler_State; Item : in out Expression) is
      Instruction_Item : Instruction;
   begin
      if Item.Kind = Open_Call then
         Item.Kind := Fixed_Register;
         Item.Info := Natural (Get (State, Item.Info).A);
      elsif Item.Kind = Open_Vararg then
         Instruction_Item := Get (State, Item.Info);
         Instruction_Item.C := 2;
         Put (State, Item.Info, Instruction_Item);
         Item.Kind := Relocatable;
      end if;
   end Set_One_Return;

   procedure Discharge_Variables (State : in out Compiler_State; Item : in out Expression) is
      Position : Natural;
   begin
      case Item.Kind is
         when Compile_Time_Constant =>
            Constant_To_Expression (Variable (State, Item.Info).Value, Item);
         when Local_Register =>
            Item.Info := Item.Register;
            Item.Kind := Fixed_Register;
         when Upvalue_Slot =>
            Code_ABC (State, Get_Upvalue, 0, Item.Info, 0, False, Position);
            Item.Info := Position;
            Item.Kind := Relocatable;
         when Indexed_Upvalue =>
            Code_ABC (State, Get_Table_Upvalue, 0, Item.Table, Item.Key, False, Position);
            Item.Info := Position;
            Item.Kind := Relocatable;
         when Indexed_Integer =>
            Free_Register (State, Item.Table);
            Code_ABC (State, Get_Integer, 0, Item.Table, Item.Key, False, Position);
            Item.Info := Position;
            Item.Kind := Relocatable;
         when Indexed_String =>
            Free_Register (State, Item.Table);
            Code_ABC (State, Get_Field, 0, Item.Table, Item.Key, False, Position);
            Item.Info := Position;
            Item.Kind := Relocatable;
         when Indexed_Register =>
            Free_Registers (State, Natural'Min (Item.Table, 255), Natural'Min (Item.Key, 255));
            Code_ABC (State, Get_Table, 0, Item.Table, Item.Key, False, Position);
            Item.Info := Position;
            Item.Kind := Relocatable;
         when Open_Vararg | Open_Call =>
            Set_One_Return (State, Item);
         when others =>
            null;
      end case;
   end Discharge_Variables;

   --  [puc lcode.c:discharge2reg].
   procedure Discharge_To_Register
     (State : in out Compiler_State; Item : in out Expression; Register : Natural)
   is
      Ignored          : Natural;
      Instruction_Item : Instruction;
   begin
      Discharge_Variables (State, Item);
      case Item.Kind is
         when Nil_Value =>
            Load_Nil (State, Register, 1);
         when False_Value =>
            Code_ABC (State, Load_False, Register, 0, 0, False, Ignored);
         when True_Value =>
            Code_ABC (State, Load_True, Register, 0, 0, False, Ignored);
         when String_Value | Constant_Index =>
            if Item.Kind = String_Value then
               String_To_Constant (State, Item);
            end if;
            Code_Constant (State, Register, Item.Info);
         when Float_Value =>
            Load_Float (State, Register, Item.Float_Bits);
         when Integer_Value =>
            Load_Integer (State, Register, Item.Integer_Bits);
         when Relocatable =>
            Instruction_Item := Get (State, Item.Info);
            if Register > 255 then
               Fail (State);
               return;
            end if;
            Instruction_Item.A := Byte (Register);
            Put (State, Item.Info, Instruction_Item);
         when Fixed_Register =>
            if Register /= Item.Info then
               Code_ABC (State, Move, Register, Item.Info, 0, False, Ignored);
            end if;
         when others =>
            return;
      end case;
      Item.Info := Register;
      Item.Kind := Fixed_Register;
   end Discharge_To_Register;

   --  [puc lcode.c:discharge2anyreg].
   procedure Discharge_To_Any_Register (State : in out Compiler_State; Item : in out Expression)
   is
   begin
      if Item.Kind /= Fixed_Register then
         Reserve_Registers (State, 1);
         if State.Failed or else Current (State).Free_Register = 0 then
            Fail (State);
            return;
         end if;
         Discharge_To_Register (State, Item, Current (State).Free_Register - 1);
      end if;
   end Discharge_To_Any_Register;

   --  [puc lcode.c:code_loadbool].
   procedure Code_Load_Boolean
     (State : in out Compiler_State; Register : Natural; Operation : Opcode; Result : out Natural)
   is
      Ignored : Natural;
   begin
      Get_Label (State, Ignored);
      Code_ABC (State, Operation, Register, 0, 0, False, Result);
   end Code_Load_Boolean;

   --  [puc lcode.c:need_value].
   function Need_Value (State : Compiler_State; List : Jump_List) return Boolean is
      Position : Jump_List := List;
   begin
      for Step in 0 .. PC (State) loop
         exit when Position = No_Jump;
         if Get (State, Jump_Control (State, Position)).Operation /= Test_Set then
            return True;
         end if;
         Position := Next_Jump (State, Position);
      end loop;
      return False;
   end Need_Value;

   --  [puc lcode.c:exp2reg].
   procedure Expression_To_Register
     (State : in out Compiler_State; Item : in out Expression; Register : Natural)
   is
      Final          : Natural;
      Load_False_At  : Natural := Natural'Last;
      Load_True_At   : Natural := Natural'Last;
      False_Jump     : Jump_List;
   begin
      Discharge_To_Register (State, Item, Register);
      if Item.Kind = Comparison then
         Concatenate_Jumps (State, Item.True_List, As_Jump (Item.Info));
      end if;
      if Has_Jumps (Item) then
         if Need_Value (State, Item.True_List) or else Need_Value (State, Item.False_List) then
            if Item.Kind = Comparison then
               False_Jump := No_Jump;
            else
               Jump (State, False_Jump);
            end if;
            Code_Load_Boolean (State, Register, Load_False_Skip, Load_False_At);
            Code_Load_Boolean (State, Register, Load_True, Load_True_At);
            Patch_To_Here (State, False_Jump);
         end if;
         Get_Label (State, Final);
         --  [puc] NO_JUMP as a default target only arises for lists of TESTSETs alone.
         Patch_List_Auxiliary (State, Item.False_List, Final, Register,
                               (if Load_False_At = Natural'Last then Final else Load_False_At));
         Patch_List_Auxiliary (State, Item.True_List, Final, Register,
                               (if Load_True_At = Natural'Last then Final else Load_True_At));
      end if;
      Item.False_List := No_Jump;
      Item.True_List := No_Jump;
      Item.Info := Register;
      Item.Kind := Fixed_Register;
   end Expression_To_Register;

   procedure To_Next_Register (State : in out Compiler_State; Item : in out Expression) is
   begin
      Discharge_Variables (State, Item);
      Free_Expression (State, Item);
      Reserve_Registers (State, 1);
      if State.Failed or else Current (State).Free_Register = 0 then
         Fail (State);
         return;
      end if;
      Expression_To_Register (State, Item, Current (State).Free_Register - 1);
   end To_Next_Register;

   procedure To_Any_Register
     (State : in out Compiler_State; Item : in out Expression; Register : out Natural)
   is
   begin
      Discharge_Variables (State, Item);
      if Item.Kind = Fixed_Register then
         if not Has_Jumps (Item) then
            Register := Item.Info;
            return;
         end if;
         if Item.Info >= Variables_On_Stack (State) then
            Expression_To_Register (State, Item, Item.Info);
            Register := Item.Info;
            return;
         end if;
      end if;
      To_Next_Register (State, Item);
      Register := Item.Info;
   end To_Any_Register;

   procedure To_Any_Register_Or_Upvalue (State : in out Compiler_State;
                                         Item : in out Expression)
   is
      Ignored : Natural;
   begin
      if Item.Kind /= Upvalue_Slot or else Has_Jumps (Item) then
         To_Any_Register (State, Item, Ignored);
      end if;
   end To_Any_Register_Or_Upvalue;

   procedure To_Value (State : in out Compiler_State; Item : in out Expression) is
      Ignored : Natural;
   begin
      if Item.Kind = Comparison or else Has_Jumps (Item) then
         To_Any_Register (State, Item, Ignored);
      else
         Discharge_Variables (State, Item);
      end if;
   end To_Value;

   --  [puc lcode.c:luaK_exp2K].
   procedure To_K (State : in out Compiler_State; Item : in out Expression; Success : out Boolean)
   is
      Index : Natural;
   begin
      Success := False;
      if Has_Jumps (Item) then
         return;
      end if;
      case Item.Kind is
         when True_Value => Simple_K (State, True_Constant, Index);
         when False_Value => Simple_K (State, False_Constant, Index);
         when Nil_Value => Simple_K (State, Nil_Constant, Index);
         when Integer_Value => Integer_K (State, Item.Integer_Bits, Index);
         when Float_Value => Number_K (State, Item.Float_Bits, Index);
         when String_Value => String_K (State, Item.String_Symbol, Item.String_Short, Index);
         when Constant_Index => Index := Item.Info;
         when others => return;
      end case;
      if Index <= Maximum_Index_RK then
         Item.Kind := Constant_Index;
         Item.Info := Index;
         Success := True;
      end if;
   end To_K;

   --  [puc lcode.c:exp2RK].
   procedure To_RK (State : in out Compiler_State; Item : in out Expression; Is_K : out Boolean)
   is
      Ignored : Natural;
   begin
      To_K (State, Item, Is_K);
      if not Is_K then
         To_Any_Register (State, Item, Ignored);
      end if;
   end To_RK;

   --  [puc lcode.c:codeABRK].
   procedure Code_ABRK
     (State : in out Compiler_State; Operation : Opcode; A, B : Natural;
      Item : in out Expression)
   is
      Is_K    : Boolean;
      Ignored : Natural;
   begin
      To_RK (State, Item, Is_K);
      Code_ABC (State, Operation, A, B, Item.Info, Is_K, Ignored);
   end Code_ABRK;

   procedure Store_Variable
     (State : in out Compiler_State; Target : Expression; Value : in out Expression)
   is
      Register : Natural;
      Ignored  : Natural;
   begin
      case Target.Kind is
         when Local_Register =>
            Free_Expression (State, Value);
            Expression_To_Register (State, Value, Target.Register);
            return;
         when Upvalue_Slot =>
            To_Any_Register (State, Value, Register);
            Code_ABC (State, Set_Upvalue, Register, Target.Info, 0, False, Ignored);
         when Indexed_Upvalue =>
            Code_ABRK (State, Set_Table_Upvalue, Target.Table, Target.Key, Value);
         when Indexed_Integer =>
            Code_ABRK (State, Set_Integer, Target.Table, Target.Key, Value);
         when Indexed_String =>
            Code_ABRK (State, Set_Field, Target.Table, Target.Key, Value);
         when Indexed_Register =>
            Code_ABRK (State, Set_Table, Target.Table, Target.Key, Value);
         when others =>
            Fail (State);
            return;
      end case;
      Free_Expression (State, Value);
   end Store_Variable;

   procedure Self_Call
     (State : in out Compiler_State; Object : in out Expression; Key : in out Expression)
   is
      Object_Register : Natural;
   begin
      To_Any_Register (State, Object, Object_Register);
      Free_Expression (State, Object);
      Object.Info := Current (State).Free_Register;
      Object.Kind := Fixed_Register;
      Reserve_Registers (State, 2);
      Code_ABRK (State, Self, Object.Info, Object_Register, Key);
      Free_Expression (State, Key);
   end Self_Call;

   --  [puc lcode.c:negatecondition].
   procedure Negate_Condition (State : in out Compiler_State; Item : Expression) is
      Control : constant Natural := Jump_Control (State, Item.Info);
      Value   : Instruction := Get (State, Control);
   begin
      Value.K := not Value.K;
      Put (State, Control, Value);
   end Negate_Condition;

   --  [puc lcode.c:jumponcond].
   procedure Jump_On_Condition
     (State : in out Compiler_State; Item : in out Expression; Condition : Boolean;
      Result : out Jump_List)
   is
      Last : Instruction;
   begin
      if Item.Kind = Relocatable then
         Last := Get (State, Item.Info);
         if Last.Operation = Logical_Not then
            Remove_Last_Instruction (State);
            Conditional_Jump (State, Test, Natural (Last.B), 0, 0, not Condition, Result);
            return;
         end if;
      end if;
      Discharge_To_Any_Register (State, Item);
      Free_Expression (State, Item);
      Conditional_Jump (State, Test_Set, No_Register, Item.Info, 0, Condition, Result);
   end Jump_On_Condition;

   procedure Go_If_True (State : in out Compiler_State; Item : in out Expression) is
      Position : Jump_List;
   begin
      Discharge_Variables (State, Item);
      case Item.Kind is
         when Comparison =>
            Negate_Condition (State, Item);
            Position := As_Jump (Item.Info);
         when Constant_Index | Float_Value | Integer_Value | String_Value | True_Value =>
            Position := No_Jump;
         when others =>
            Jump_On_Condition (State, Item, False, Position);
      end case;
      Concatenate_Jumps (State, Item.False_List, Position);
      Patch_To_Here (State, Item.True_List);
      Item.True_List := No_Jump;
   end Go_If_True;

   procedure Go_If_False (State : in out Compiler_State; Item : in out Expression) is
      Position : Jump_List;
   begin
      Discharge_Variables (State, Item);
      case Item.Kind is
         when Comparison =>
            Position := As_Jump (Item.Info);
         when Nil_Value | False_Value =>
            Position := No_Jump;
         when others =>
            Jump_On_Condition (State, Item, True, Position);
      end case;
      Concatenate_Jumps (State, Item.True_List, Position);
      Patch_To_Here (State, Item.False_List);
      Item.False_List := No_Jump;
   end Go_If_False;

   --  [puc lcode.c:codenot].
   procedure Code_Not (State : in out Compiler_State; Item : in out Expression) is
      Saved : Jump_List;
   begin
      case Item.Kind is
         when Nil_Value | False_Value =>
            Item.Kind := True_Value;
         when Constant_Index | Float_Value | Integer_Value | String_Value | True_Value =>
            Item.Kind := False_Value;
         when Comparison =>
            Negate_Condition (State, Item);
         when Relocatable | Fixed_Register =>
            Discharge_To_Any_Register (State, Item);
            Free_Expression (State, Item);
            Code_ABC (State, Logical_Not, 0, Item.Info, 0, False, Item.Info);
            Item.Kind := Relocatable;
         when others =>
            Fail (State);
      end case;
      Saved := Item.False_List;
      Item.False_List := Item.True_List;
      Item.True_List := Saved;
      Remove_Values (State, Item.False_List);
      Remove_Values (State, Item.True_List);
   end Code_Not;

   --  [puc lcode.c:isKstr].
   function Is_K_String (State : Compiler_State; Item : Expression) return Boolean
   is (Item.Kind = Constant_Index
       and then not Has_Jumps (Item)
       and then Item.Info <= 255
       and then Constant_Of (State, Item.Info).Kind = Short_String_Constant);

   --  [puc lcode.c:isKint].
   function Is_K_Integer (Item : Expression) return Boolean
   is (Item.Kind = Integer_Value and then not Has_Jumps (Item));

   --  [puc lcode.c:isCint].
   function Is_C_Integer (Item : Expression) return Boolean
   is (Is_K_Integer (Item) and then Item.Integer_Bits in 0 .. Maximum_C);

   --  [puc lcode.c:isSCint].
   function Is_SC_Integer (Item : Expression) return Boolean
   is (Is_K_Integer (Item) and then Fits_C (Item.Integer_Bits));

   --  [puc lcode.c:isSCnumber]: Immediate is the excess-127 operand.
   procedure Is_SC_Number
     (Item : Expression; Result : out Boolean; Immediate : out Natural; Is_Float : out Boolean)
   is
      Value   : Integer_64;
      Success : Boolean;
   begin
      Result := False;
      Immediate := 0;
      Is_Float := False;
      if Item.Kind = Integer_Value then
         Value := Item.Integer_Bits;
      elsif Item.Kind = Float_Value then
         Floats.To_Integer (Item.Float_Bits, Value, Success);
         if not Success then
            return;
         end if;
         Is_Float := True;
      else
         return;
      end if;
      if not Has_Jumps (Item) and then Fits_C (Value) then
         Immediate := Natural (Value + Offset_sC);
         Result := True;
      end if;
   end Is_SC_Number;

   --  [puc lcode.c:isSCnumber] without its outputs.
   function Fits_SC_Number (Item : Expression) return Boolean is
      Value   : Interfaces.Integer_64;
      Success : Boolean;
   begin
      if Item.Kind = Integer_Value then
         Value := Item.Integer_Bits;
      elsif Item.Kind = Float_Value then
         Floats.To_Integer (Item.Float_Bits, Value, Success);
         if not Success then
            return False;
         end if;
      else
         return False;
      end if;
      return not Has_Jumps (Item) and then Fits_C (Value);
   end Fits_SC_Number;

   procedure Indexed
     (State : in out Compiler_State; Table : in out Expression; Key_Value : Expression)
   is
      Key      : Expression := Key_Value;
      Register : Natural;
      Ignored  : Natural;
   begin
      if Key.Kind = String_Value then
         String_To_Constant (State, Key);
      end if;
      if Table.Kind = Upvalue_Slot and then not Is_K_String (State, Key) then
         To_Any_Register (State, Table, Ignored);
      end if;
      if Table.Kind = Upvalue_Slot then
         Table.Table := Table.Info;
         Table.Key := Key.Info;
         Table.Kind := Indexed_Upvalue;
      else
         Table.Table := (if Table.Kind = Local_Register then Table.Register else Table.Info);
         if Is_K_String (State, Key) then
            Table.Key := Key.Info;
            Table.Kind := Indexed_String;
         elsif Is_C_Integer (Key) then
            Table.Key := Natural (Key.Integer_Bits);
            Table.Kind := Indexed_Integer;
         else
            declare
               Unused_Key : Expression := Key;
            begin
               To_Any_Register (State, Unused_Key, Register);
            end;
            Table.Key := Register;
            Table.Kind := Indexed_Register;
         end if;
      end if;
   end Indexed;

   --  [puc lcode.c:tonumeral].
   function Is_Numeral (Item : Expression) return Boolean
   is (not Has_Jumps (Item) and then Item.Kind in Integer_Value | Float_Value);

   --  The arithmetic and bitwise operators, in lopcodes.h's (and ltm.h's) order: Add .. Shift_Right
   --  of Opcode map one to one onto them.
   function Operation_Number (Operator : Operator_Kind) return Natural
   is (case Operator is
         when Add => 0, when Subtract => 1, when Multiply => 2, when Modulo => 3,
         when Power => 4, when Divide => 5, when Floor_Divide => 6, when Bitwise_And => 7,
         when Bitwise_Or => 8, when Bitwise_Exclusive_Or => 9, when Shift_Left => 10,
         when Shift_Right => 11, when others => 0);

   --  [puc lcode.c:binopr2op] Base shifted by Operator's place.
   function Operation_Of (Operator : Operator_Kind; Base : Opcode) return Opcode
   is (if Opcode'Pos (Base) + Operation_Number (Operator) <= Opcode'Pos (Opcode'Last)
       then Opcode'Val (Opcode'Pos (Base) + Operation_Number (Operator)) else Base);

   --  [puc lcode.c:binopr2TM] The metamethod event of Operator.
   function Event_Of (Operator : Operator_Kind) return Natural
   is (Natural (First_Binary_Event) + Operation_Number (Operator));

   --  [puc lcode.c:validop and lobject.c:luaO_rawarith] Folds Left Operator Right when both
   --  are numerals; Result is the value.
   procedure Fold
     (Operator : Operator_Kind;
      Left, Right : Expression;
      Result : out Expression;
      Success : out Boolean)
   is
      Left_Integer, Right_Integer : Integer_64;
      Converted_Left, Converted_Right : Boolean;
      Left_Float, Right_Float, Value : Floats.Float_Bits;
   begin
      Result := Left;
      Success := False;
      if not Is_Numeral (Left) or else not Is_Numeral (Right) then
         return;
      end if;
      --  Integer views (bitwise operations need integral values) and float views.
      if Left.Kind = Integer_Value then
         Left_Integer := Left.Integer_Bits;
         Converted_Left := True;
         Left_Float := Floats.From_Integer (Left.Integer_Bits);
      else
         Floats.To_Integer (Left.Float_Bits, Left_Integer, Converted_Left);
         Left_Float := Left.Float_Bits;
      end if;
      if Right.Kind = Integer_Value then
         Right_Integer := Right.Integer_Bits;
         Converted_Right := True;
         Right_Float := Floats.From_Integer (Right.Integer_Bits);
      else
         Floats.To_Integer (Right.Float_Bits, Right_Integer, Converted_Right);
         Right_Float := Right.Float_Bits;
      end if;
      case Operator is
         when Bitwise_And | Bitwise_Or | Bitwise_Exclusive_Or | Shift_Left | Shift_Right
            | Bitwise_Not =>
            if not Converted_Left or else not Converted_Right then
               return;
            end if;
            Result.Kind := Integer_Value;
            Result.Integer_Bits :=
              (case Operator is
                 when Bitwise_And => Integer_Arithmetic.Bitwise_And (Left_Integer, Right_Integer),
                 when Bitwise_Or => Integer_Arithmetic.Bitwise_Or (Left_Integer, Right_Integer),
                 when Bitwise_Exclusive_Or =>
                   Integer_Arithmetic.Bitwise_Exclusive_Or (Left_Integer, Right_Integer),
                 when Shift_Left => Integer_Arithmetic.Shift_Left (Left_Integer, Right_Integer),
                 when Shift_Right =>
                   Integer_Arithmetic.Shift_Left
                     (Left_Integer, Integer_Arithmetic.Negate (Right_Integer)),
                 when others => Integer_Arithmetic.Bitwise_Not (Left_Integer));
            Success := True;
            return;
         when Divide | Floor_Divide | Modulo =>
            if Floats.Is_Zero (Right_Float) then
               return;
            end if;
         when others =>
            null;
      end case;
      if Operator not in Divide | Power and then Left.Kind = Integer_Value
        and then Right.Kind = Integer_Value
      then
         if Operator in Floor_Divide | Modulo and then Right_Integer = 0 then
            return;
         end if;
         Result.Kind := Integer_Value;
         Result.Integer_Bits :=
           (case Operator is
              when Add => Integer_Arithmetic.Add (Left_Integer, Right_Integer),
              when Subtract => Integer_Arithmetic.Subtract (Left_Integer, Right_Integer),
              when Multiply => Integer_Arithmetic.Multiply (Left_Integer, Right_Integer),
              when Floor_Divide =>
                (if Right_Integer /= 0
                 then Integer_Arithmetic.Floor_Divide (Left_Integer, Right_Integer) else 0),
              when Modulo =>
                (if Right_Integer /= 0
                 then Integer_Arithmetic.Modulo (Left_Integer, Right_Integer) else 0),
              when others => Integer_Arithmetic.Negate (Left_Integer));
         Success := True;
         return;
      end if;
      Value := Floats.Arithmetic
        ((case Operator is
            when Add => Floats.Add,
            when Subtract => Floats.Subtract,
            when Multiply => Floats.Multiply,
            when Divide => Floats.Divide,
            when Power => Floats.Power,
            when Floor_Divide => Floats.Floor_Divide,
            when Modulo => Floats.Modulo,
            when others => Floats.Negate),
         Left_Float, Right_Float);
      --  Folds neither NaN nor 0.0 (to avoid problems with -0.0).
      if Floats.Is_NaN (Value) or else Floats.Is_Zero (Value) then
         return;
      end if;
      Result.Kind := Float_Value;
      Result.Float_Bits := Value;
      Success := True;
   end Fold;

   --  [puc lcode.c:codeunexpval].
   procedure Code_Unary_Value
     (State : in out Compiler_State; Operation : Opcode; Item : in out Expression;
      Line : Line_Number)
   is
      Register : Natural;
   begin
      To_Any_Register (State, Item, Register);
      Free_Expression (State, Item);
      Code_ABC (State, Operation, 0, Register, 0, False, Item.Info);
      Item.Kind := Relocatable;
      Fix_Line (State, Line);
   end Code_Unary_Value;

   --  [puc lcode.c:finishbinexpval].
   procedure Finish_Binary_Value
     (State : in out Compiler_State;
      Left : in out Expression;
      Right : Expression;
      Operation : Opcode;
      Second : Natural;
      Flip : Boolean;
      Line : Line_Number;
      Metamethod : Opcode;
      Event : Natural)
   is
      First   : Natural;
      Ignored : Natural;
   begin
      To_Any_Register (State, Left, First);
      Code_ABC (State, Operation, 0, First, Second, False, Ignored);
      Free_Expressions (State, Left, Right);
      Left.Info := Ignored;
      Left.Kind := Relocatable;
      Fix_Line (State, Line);
      Code_ABC (State, Metamethod, First, Second, Event, Flip, Ignored);
      Fix_Line (State, Line);
   end Finish_Binary_Value;

   --  [puc lcode.c:codebinexpval].
   procedure Code_Binary_Value
     (State : in out Compiler_State; Operator : Operator_Kind;
      Left, Right : in out Expression; Line : Line_Number)
   is
      Second : Natural;
   begin
      To_Any_Register (State, Right, Second);
      Finish_Binary_Value (State, Left, Right, Operation_Of (Operator, Add), Second, False,
                           Line, Metamethod_Binary, Event_Of (Operator));
   end Code_Binary_Value;

   --  [puc lcode.c:codebini].
   procedure Code_Binary_Immediate
     (State : in out Compiler_State; Operation : Opcode; Left : in out Expression;
      Right : Expression; Flip : Boolean; Line : Line_Number; Event : Natural)
   is
   begin
      if not Fits_C (Right.Integer_Bits) then
         Fail (State);
         return;
      end if;
      Finish_Binary_Value (State, Left, Right, Operation, Excess (Right.Integer_Bits),
                           Flip, Line, Metamethod_Binary_Integer, Event);
   end Code_Binary_Immediate;

   --  [puc lcode.c:codebinK].
   procedure Code_Binary_K
     (State : in out Compiler_State; Operator : Operator_Kind; Left : in out Expression;
      Right : Expression; Flip : Boolean; Line : Line_Number)
   is
   begin
      Finish_Binary_Value (State, Left, Right, Operation_Of (Operator, Add_Constant), Right.Info,
                           Flip, Line, Metamethod_Binary_Constant, Event_Of (Operator));
   end Code_Binary_K;

   --  [puc lcode.c:finishbinexpneg].
   procedure Finish_Binary_Negated
     (State : in out Compiler_State; Left : in out Expression; Right : Expression;
      Operation : Opcode; Line : Line_Number; Event : Natural; Success : out Boolean)
   is
      Value : Integer_64;
      Item  : Instruction;
   begin
      Success := False;
      if not Is_K_Integer (Right) then
         return;
      end if;
      Value := Right.Integer_Bits;
      if not Fits_C (Value) or else not Fits_C (-Value) then
         return;
      end if;
      Finish_Binary_Value (State, Left, Right, Operation, Excess (-Value), False,
                           Line, Metamethod_Binary_Integer, Event);
      if PC (State) = 0 then
         Fail (State);
         return;
      end if;
      Item := Get (State, PC (State) - 1);
      Item.B := Byte (Excess (Value));
      Put (State, PC (State) - 1, Item);
      Success := True;
   end Finish_Binary_Negated;

   --  [puc lcode.c:swapexps].
   procedure Swap (Left, Right : in out Expression) is
      Saved : constant Expression := Left;
   begin
      Left := Right;
      Right := Saved;
   end Swap;

   --  [puc lcode.c:codebinNoK].
   procedure Code_Binary_No_K
     (State : in out Compiler_State; Operator : Operator_Kind; Left, Right : in out Expression;
      Flip : Boolean; Line : Line_Number)
   is
   begin
      if Flip then
         Swap (Left, Right);
      end if;
      Code_Binary_Value (State, Operator, Left, Right, Line);
   end Code_Binary_No_K;

   --  [puc lcode.c:codearith].
   procedure Code_Arithmetic
     (State : in out Compiler_State; Operator : Operator_Kind; Left, Right : in out Expression;
      Flip : Boolean; Line : Line_Number)
   is
      Is_K : Boolean := False;
   begin
      if Is_Numeral (Right) then
         To_K (State, Right, Is_K);
      end if;
      if Is_K then
         Code_Binary_K (State, Operator, Left, Right, Flip, Line);
      else
         Code_Binary_No_K (State, Operator, Left, Right, Flip, Line);
      end if;
   end Code_Arithmetic;

   --  [puc lcode.c:codecommutative].
   procedure Code_Commutative
     (State : in out Compiler_State; Operator : Operator_Kind; Left, Right : in out Expression;
      Line : Line_Number)
   is
      Flip : Boolean := False;
   begin
      if Is_Numeral (Left) then
         Swap (Left, Right);
         Flip := True;
      end if;
      if Operator = Add and then Is_SC_Integer (Right) then
         Code_Binary_Immediate (State, Add_Integer, Left, Right, Flip, Line, Event_Of (Add));
      else
         Code_Arithmetic (State, Operator, Left, Right, Flip, Line);
      end if;
   end Code_Commutative;

   --  [puc lcode.c:codebitwise].
   procedure Code_Bitwise
     (State : in out Compiler_State; Operator : Operator_Kind; Left, Right : in out Expression;
      Line : Line_Number)
   is
      Flip : Boolean := False;
      Is_K : Boolean := False;
   begin
      if Left.Kind = Integer_Value then
         Swap (Left, Right);
         Flip := True;
      end if;
      if Right.Kind = Integer_Value then
         To_K (State, Right, Is_K);
      end if;
      if Is_K then
         Code_Binary_K (State, Operator, Left, Right, Flip, Line);
      else
         Code_Binary_No_K (State, Operator, Left, Right, Flip, Line);
      end if;
   end Code_Bitwise;

   --  [puc lcode.c:codeorder] for < and <= (Operator Less or Less_Equal).
   procedure Code_Order
     (State : in out Compiler_State; Operator : Operator_Kind; Left, Right : in out Expression)
   is
      First, Second : Natural;
      Immediate     : Natural;
      Is_Float      : Boolean;
      Found         : Boolean;
      Operation     : Opcode;
      Position      : Jump_List;
      Offset        : constant Natural := (if Operator = Less_Equal then 1 else 0);
   begin
      Is_SC_Number (Right, Found, Immediate, Is_Float);
      if Found then
         To_Any_Register (State, Left, First);
         Second := Immediate;
         Operation := Opcode'Val (Opcode'Pos (Less_Than_Integer) + Offset);
      else
         Is_SC_Number (Left, Found, Immediate, Is_Float);
         if Found then
            To_Any_Register (State, Right, First);
            Second := Immediate;
            Operation := Opcode'Val (Opcode'Pos (Greater_Than_Integer) + Offset);
         else
            Is_Float := False;
            To_Any_Register (State, Left, First);
            To_Any_Register (State, Right, Second);
            Operation := Opcode'Val (Opcode'Pos (Less_Than) + Offset);
         end if;
      end if;
      Free_Expressions (State, Left, Right);
      Conditional_Jump (State, Operation, First, Second, Boolean'Pos (Is_Float), True, Position);
      Left.Info := (if Position = No_Jump then 0 else Position);
      Left.Kind := Comparison;
   end Code_Order;

   --  [puc lcode.c:codeeq].
   procedure Code_Equal
     (State : in out Compiler_State; Operator : Operator_Kind; Left, Right : in out Expression)
   is
      First, Second : Natural;
      Immediate     : Natural;
      Is_Float      : Boolean;
      Found         : Boolean;
      Is_K          : Boolean;
      Operation     : Opcode;
      Position      : Jump_List;
   begin
      if Left.Kind /= Fixed_Register then
         Swap (Left, Right);
      end if;
      To_Any_Register (State, Left, First);
      Is_SC_Number (Right, Found, Immediate, Is_Float);
      if Found then
         Operation := Equal_Integer;
         Second := Immediate;
      else
         To_RK (State, Right, Is_K);
         if Is_K then
            Operation := Equal_Constant;
            Second := Right.Info;
         else
            Operation := Equal;
            To_Any_Register (State, Right, Second);
         end if;
      end if;
      Free_Expressions (State, Left, Right);
      Conditional_Jump (State, Operation, First, Second, Boolean'Pos (Is_Float),
                        Operator = Equal, Position);
      Left.Info := (if Position = No_Jump then 0 else Position);
      Left.Kind := Comparison;
   end Code_Equal;

   procedure Prefix
     (State : in out Compiler_State;
      Operator : Operator_Kind;
      Item : in out Expression;
      Line : Line_Number)
   is
      Zero    : constant Expression := (Kind => Integer_Value, others => <>);
      Folded  : Expression;
      Success : Boolean;
   begin
      Discharge_Variables (State, Item);
      case Operator is
         when Negate | Bitwise_Not =>
            Fold (Operator, Item, Zero, Folded, Success);
            if Success then
               Item := Folded;
            else
               Code_Unary_Value (State, (if Operator = Negate then Bytecode.Negate
                                         else Bytecode.Bitwise_Not), Item, Line);
            end if;
         when Length =>
            Code_Unary_Value (State, Bytecode.Length, Item, Line);
         when Logical_Not =>
            Code_Not (State, Item);
         when others =>
            Fail (State);
      end case;
   end Prefix;

   procedure Infix
     (State : in out Compiler_State; Operator : Operator_Kind; Item : in out Expression)
   is
      Ignored   : Natural;
      Unused    : Boolean;
   begin
      Discharge_Variables (State, Item);
      case Operator is
         when And_Then =>
            Go_If_True (State, Item);
         when Or_Else =>
            Go_If_False (State, Item);
         when Concatenate =>
            To_Next_Register (State, Item);
         when Add | Subtract | Multiply | Divide | Floor_Divide | Modulo | Power | Bitwise_And
            | Bitwise_Or | Bitwise_Exclusive_Or | Shift_Left | Shift_Right =>
            if not Is_Numeral (Item) then
               To_Any_Register (State, Item, Ignored);
            end if;
         when Equal | Not_Equal =>
            if not Is_Numeral (Item) then
               To_RK (State, Item, Unused);
            end if;
         when Less | Less_Equal | Greater | Greater_Equal =>
            if not Fits_SC_Number (Item) then
               To_Any_Register (State, Item, Ignored);
            end if;
         when others =>
            Fail (State);
      end case;
   end Infix;

   --  [puc lcode.c:codeconcat].
   procedure Code_Concatenation
     (State : in out Compiler_State; Left, Right : Expression; Line : Line_Number)
   is
      Previous : Instruction;
      Exists   : Boolean;
      Ignored  : Natural;
   begin
      Previous_Instruction (State, Previous, Exists);
      if Left.Info > 255 then
         Fail (State);
         return;
      end if;
      if Exists and then Previous.Operation = Concatenate then
         Free_Expression (State, Right);
         if Previous.B = 255 then
            Fail (State);
            return;
         end if;
         Previous.A := Byte (Left.Info);
         Previous.B := Previous.B + 1;
         if PC (State) = 0 then
            Fail (State);
            return;
         end if;
         Put (State, PC (State) - 1, Previous);
      else
         Code_ABC (State, Concatenate, Left.Info, 2, 0, False, Ignored);
         Free_Expression (State, Right);
         Fix_Line (State, Line);
      end if;
   end Code_Concatenation;

   procedure Posfix
     (State : in out Compiler_State;
      Operator : Operator_Kind;
      Left : in out Expression;
      Right : in out Expression;
      Line : Line_Number)
   is
      Folded  : Expression;
      Success : Boolean;
   begin
      Discharge_Variables (State, Right);
      if Operator in Add | Subtract | Multiply | Divide | Floor_Divide | Modulo | Power
                   | Bitwise_And | Bitwise_Or | Bitwise_Exclusive_Or | Shift_Left | Shift_Right
      then
         Fold (Operator, Left, Right, Folded, Success);
         if Success then
            Left := Folded;
            return;
         end if;
      end if;
      case Operator is
         when And_Then =>
            Concatenate_Jumps (State, Right.False_List, Left.False_List);
            Left := Right;
         when Or_Else =>
            Concatenate_Jumps (State, Right.True_List, Left.True_List);
            Left := Right;
         when Concatenate =>
            To_Next_Register (State, Right);
            Code_Concatenation (State, Left, Right, Line);
         when Add | Multiply =>
            Code_Commutative (State, Operator, Left, Right, Line);
         when Subtract =>
            Finish_Binary_Negated (State, Left, Right, Add_Integer, Line, Event_Of (Subtract),
                                   Success);
            if not Success then
               Code_Arithmetic (State, Operator, Left, Right, False, Line);
            end if;
         when Divide | Floor_Divide | Modulo | Power =>
            Code_Arithmetic (State, Operator, Left, Right, False, Line);
         when Bitwise_And | Bitwise_Or | Bitwise_Exclusive_Or =>
            Code_Bitwise (State, Operator, Left, Right, Line);
         when Shift_Left =>
            if Is_SC_Integer (Left) then
               Swap (Left, Right);
               Code_Binary_Immediate (State, Shift_Left_Integer, Left, Right, True, Line,
                                      Event_Of (Shift_Left));
            else
               Finish_Binary_Negated (State, Left, Right, Shift_Right_Integer, Line,
                                      Event_Of (Shift_Left), Success);
               if not Success then
                  Code_Binary_Value (State, Operator, Left, Right, Line);
               end if;
            end if;
         when Shift_Right =>
            if Is_SC_Integer (Right) then
               Code_Binary_Immediate (State, Shift_Right_Integer, Left, Right, False, Line,
                                      Event_Of (Shift_Right));
            else
               Code_Binary_Value (State, Operator, Left, Right, Line);
            end if;
         when Equal | Not_Equal =>
            Code_Equal (State, Operator, Left, Right);
         when Greater | Greater_Equal =>
            Swap (Left, Right);
            Code_Order (State, (if Operator = Greater then Less else Less_Equal), Left, Right);
         when Less | Less_Equal =>
            Code_Order (State, Operator, Left, Right);
         when others =>
            Fail (State);
      end case;
   end Posfix;

   procedure Set_Table_Size
     (State : in out Compiler_State; Index, Register, Array_Size, Hash_Size : Natural)
   is
      Hash_Bits : Natural := 0;
      Size      : Natural := 1;
      Extra     : constant Natural := Array_Size / (Maximum_C + 1);
   begin
      if Hash_Size /= 0 then
         --  [puc lobject.c:luaO_ceillog2] + 1.
         while Size < Hash_Size and then Size <= 2 ** 28 and then Hash_Bits < 29 loop
            pragma Loop_Variant (Increases => Hash_Bits);
            Size := Size * 2;
            Hash_Bits := Hash_Bits + 1;
         end loop;
         Hash_Bits := Hash_Bits + 1;
      end if;
      if Register > 255 or else Extra > Maximum_Ax or else Index = Natural'Last then
         Fail (State);
         return;
      end if;
      Put (State, Index, (Operation => New_Table, A => Byte (Register), B => Byte (Hash_Bits),
                          C => Byte (Array_Size mod (Maximum_C + 1)), K => Extra > 0,
                          Wide => 0));
      Put (State, Index + 1, (Operation => Extra_Argument, Wide => Wide_Argument (Extra),
                              others => <>));
   end Set_Table_Size;

   procedure Set_List
     (State : in out Compiler_State; Base, Count : Natural; To_Store : Integer)
   is
      Stored  : constant Natural := (if To_Store = Multiple_Results then 0
                                     elsif To_Store in 0 .. 255 then To_Store else 0);
      Ignored : Natural;
      Item    : Function_Entry;
   begin
      if Count <= Maximum_C then
         Code_ABC (State, Set_List, Base, Stored, Count, False, Ignored);
      else
         Code_ABC (State, Set_List, Base, Stored, Count mod (Maximum_C + 1), True, Ignored);
         Code_Extra_Argument (State, Count / (Maximum_C + 1));
      end if;
      Item := Current (State);
      if Base >= Maximum_Registers then
         Fail (State);
         return;
      end if;
      Item.Free_Register := Base + 1;
      Set_Current (State, Item);
   end Set_List;

   --  [puc lcode.c:finaltarget].
   function Final_Target (State : Compiler_State; Start : Natural) return Natural is
      Position : Natural := Start;
      Item     : Instruction;
   begin
      for Count in 1 .. 100 loop
         Item := Get (State, Position);
         exit when Item.Operation /= Jump;
         exit when Position + 1 + Integer (Item.Wide) - Offset_sJ not in 0 .. Entry_Number'Last;
         Position := Position + 1 + Integer (Item.Wide) - Offset_sJ;
      end loop;
      return Position;
   end Final_Target;

   procedure Finish (State : in out Compiler_State) is
      Item  : Instruction;
      Facts : constant Prototype_Header := Current (State).Facts;
      Close : constant Boolean := Current (State).Needs_Close;
   begin
      for Index in 0 .. PC (State) - 1 loop
         Item := Get (State, Index);
         case Item.Operation is
            when Return_None | Return_One | Bytecode.Return_Values | Tail_Call =>
               if Item.Operation in Return_None | Return_One
                 and then (Close or else Facts.Is_Vararg)
               then
                  Item.Operation := Bytecode.Return_Values;
               end if;
               if Item.Operation in Bytecode.Return_Values | Tail_Call then
                  if Close then
                     Item.K := True;
                  end if;
                  if Facts.Is_Vararg then
                     Item.C := Facts.Parameter_Count + (if Facts.Parameter_Count < 255 then 1
                                                        else 0);
                  end if;
                  Put (State, Index, Item);
               end if;
            when Jump =>
               Fix_Jump (State, Index, Final_Target (State, Index));
            when others =>
               null;
         end case;
      end loop;
   end Finish;

end Pyro.Compiler.Code;
