--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  Functions, blocks, local variables, upvalues, labels and gotos as PUC Lua's lparser.c keeps
--  them while it generates code.

with Pyro.Diagnostics; use Pyro.Diagnostics;

package body Pyro.Compiler.Code.Scopes with SPARK_Mode => On is

   --  The position after Index.
   function Next_Position (Index : Natural) return Work_Position
   is (Work_Position (Index + 1))
   with Pre => Index < Natural (Work_Position'Last);

   --  The number of open functions.
   function Depth (State : Compiler_State) return Natural
   is (Natural (Function_Arrays.Length (State.Functions)));

   --  The open function at Level (1 is the main function).
   function Function_At (State : Compiler_State; Level : Natural) return Function_Entry
   is (if Level in 1 .. Depth (State)
       then Function_Arrays.Element (State.Functions, Work_Position (Level))
       else (others => <>));

   procedure Set_Function_At
     (State : in out Compiler_State; Level : Natural; Item : Function_Entry)
   is
   begin
      if Level in 1 .. Depth (State) then
         Function_Arrays.Replace_Element (State.Functions, Work_Position (Level), Item);
      else
         Fail (State);
      end if;
   end Set_Function_At;

   --  The position of the open block of the function at Level, or 0.
   function Block_Position (State : Compiler_State; Level : Natural) return Natural
   is (if Level in 1 .. Depth (State) - 1
       then Function_At (State, Level + 1).Block_Base
       elsif Level = Depth (State) then Natural (Block_Arrays.Length (State.Blocks))
       else 0);

   function Block_At (State : Compiler_State; Position : Natural) return Block_Entry
   is (if Position in 1 .. Natural (Block_Arrays.Length (State.Blocks))
       then Block_Arrays.Element (State.Blocks, Work_Position (Position))
       else (others => <>));

   procedure Set_Block_At
     (State : in out Compiler_State; Position : Natural; Item : Block_Entry)
   is
   begin
      if Position in 1 .. Natural (Block_Arrays.Length (State.Blocks)) then
         Block_Arrays.Replace_Element (State.Blocks, Work_Position (Position), Item);
      else
         Fail (State);
      end if;
   end Set_Block_At;

   function Block_Has_Upvalue (State : Compiler_State) return Boolean
   is (Block_At (State, Block_Position (State, Depth (State))).Has_Upvalue);

   function Inside_To_Be_Closed (State : Compiler_State) return Boolean
   is (Block_At (State, Block_Position (State, Depth (State))).Inside_To_Be_Closed);

   --  The upvalue slot Index of the function at Level, or 0.
   function Upvalue_Position (Level, Index : Natural) return Natural
   is (if Level in 1 .. 2 ** 16 and then Index < Maximum_Upvalues
       then (Level - 1) * Maximum_Upvalues + Index + 1 else 0);

   function Upvalue_At (State : Compiler_State; Level, Index : Natural) return Upvalue_Entry
   is (if Upvalue_Position (Level, Index)
            in 1 .. Natural (Upvalue_Arrays.Length (State.Upvalues))
       then Upvalue_Arrays.Element
              (State.Upvalues, Work_Position (Upvalue_Position (Level, Index)))
       else (others => <>));

   --  The debug record Index of the open function, by position (0 when there is none).
   function Debug_Position (State : Compiler_State; Index : Natural) return Natural
   is (if Index < Natural'Last - Current (State).Debug_Base
          and then Current (State).Debug_Base + Index
                     < Natural (Debug_Arrays.Length (State.Debug_Locals))
       then Current (State).Debug_Base + Index + 1 else 0);

   procedure Enter_Block (State : in out Compiler_State; Is_Loop : Boolean) is
      Outer   : constant Natural := Block_Position (State, Depth (State));
      Success : Boolean;
   begin
      Block_Arrays.Append
        (State.Blocks,
         (Active              => Current (State).Active,
          First_Label         => Natural (Label_Arrays.Length (State.Labels)),
          First_Goto          => Natural (Label_Arrays.Length (State.Gotos)),
          Has_Upvalue         => False,
          Is_Loop             => Is_Loop,
          Inside_To_Be_Closed =>
            Outer > Current (State).Block_Base
            and then Block_At (State, Outer).Inside_To_Be_Closed),
         State.Budget, Success);
      if not Success then
         Raise_Error (State, Not_Enough_Memory, 0);
      end if;
   end Enter_Block;

   procedure Set_Debug_Start (State : in out Compiler_State; Index : Natural; Start : Natural) is
      Position : constant Natural := Debug_Position (State, Index);
      Item     : Local_Variable;
   begin
      if Position = 0 or else Start > Entry_Count'Last then
         Fail (State);
         return;
      end if;
      Item := Debug_Arrays.Element (State.Debug_Locals, Work_Position (Position));
      Item.Start_PC := Start;
      Debug_Arrays.Replace_Element (State.Debug_Locals, Work_Position (Position), Item);
   end Set_Debug_Start;

   --  [puc lparser.c:removevars].
   procedure Remove_Variables (State : in out Compiler_State; To_Level : Natural) is
      Item     : Function_Entry := Current (State);
      Variable : Variable_Entry;
      Position : Natural;
      Debug    : Local_Variable;
   begin
      if Item.Active < To_Level or else State.Variable_Count < Item.Active - To_Level then
         Fail (State);
         return;
      end if;
      State.Variable_Count := State.Variable_Count - (Item.Active - To_Level);
      while Item.Active > To_Level loop
         pragma Loop_Variant (Decreases => Item.Active);
         Item.Active := Item.Active - 1;
         Variable := Local_Variable_Of (State, Item.Active);
         if Variable.Kind /= Compile_Time_Variable then
            Position := Debug_Position (State, Variable.Debug_Index);
            if Position /= 0 then
               Debug := Debug_Arrays.Element (State.Debug_Locals, Work_Position (Position));
               Debug.End_PC := Natural'Min (PC (State), Entry_Count'Last);
               Debug_Arrays.Replace_Element (State.Debug_Locals, Work_Position (Position), Debug);
            end if;
         end if;
      end loop;
      Set_Current (State, Item);
   end Remove_Variables;

   --  [puc lparser.c:solvegotos] Patches the pending gotos of the open block to Label;
   --  Needs_Close is whether one of them needs a CLOSE.
   procedure Solve_Gotos
     (State : in out Compiler_State; Label : Label_Entry; Needs_Close : out Boolean)
   is
      Index : Natural := Block_At (State, Block_Position (State, Depth (State))).First_Goto;
      Item  : Label_Entry;
   begin
      Needs_Close := False;
      --  Each step either removes a goto or moves past one.
      for Step in 1 .. Natural (Label_Arrays.Length (State.Gotos)) loop
         exit when Index >= Natural (Label_Arrays.Length (State.Gotos));
         pragma Assert (Index < Natural (Label_Arrays.Length (State.Gotos)));
         Item := Label_Arrays.Element (State.Gotos, Next_Position (Index));
         if Item.Name = Label.Name then
            Needs_Close := Needs_Close or else Item.Close;
            --  A goto into a variable's scope: the resolver reports it; in a chunk with errors
            --  compiling goes on past it, so that later limit errors are found.
            if Item.Active < Label.Active and then not State.Partial then
               Fail (State);
               return;
            end if;
            Patch_List (State, Item.PC, Natural'Max (Label.PC, 0));
            exit when Index >= Natural (Label_Arrays.Length (State.Gotos));
            --  Removes the goto, keeping the others in order.
            for Moved in Index + 1 .. Natural (Label_Arrays.Length (State.Gotos)) - 1 loop
               pragma Loop_Invariant
                 (Label_Arrays.Length (State.Gotos)
                  = Label_Arrays.Length (State.Gotos)'Loop_Entry);
               Label_Arrays.Replace_Element
                 (State.Gotos, Work_Position (Moved),
                  Label_Arrays.Element (State.Gotos, Work_Position (Moved + 1)));
            end loop;
            Label_Arrays.Truncate (State.Gotos, Label_Arrays.Length (State.Gotos) - 1);
         else
            Index := Index + 1;
         end if;
      end loop;
   end Solve_Gotos;

   procedure Create_Label
     (State : in out Compiler_State;
      Name : Symbol_Index;
      Line : Line_Number;
      Last : Boolean;
      Needed_Close : out Boolean)
   is
      Label   : Label_Entry;
      Here    : Natural;
      Success : Boolean;
      Ignored : Natural;
   begin
      Needed_Close := False;
      Get_Label (State, Here);
      if Here > Entry_Number'Last then
         Fail (State);
         return;
      end if;
      Label := (Name => Name, Line => Line, Active => Current (State).Active, Close => False,
                PC => Here);
      if Last then
         Label.Active := Block_At (State, Block_Position (State, Depth (State))).Active;
      end if;
      if Label_Arrays.Length (State.Labels) >= Maximum_Labels then
         Raise_Error (State, Too_Many_Labels, 0);
         return;
      end if;
      Label_Arrays.Append (State.Labels, Label, State.Budget, Success);
      if not Success then
         Raise_Error (State, Not_Enough_Memory, 0);
         return;
      end if;
      Solve_Gotos (State, Label, Needed_Close);
      if Needed_Close then
         Code_ABC (State, Close, Variables_On_Stack (State), 0, 0, False, Ignored);
      end if;
   end Create_Label;

   --  [puc lparser.c:movegotosout].
   procedure Move_Gotos_Out (State : in out Compiler_State; Block : Block_Entry) is
      Item : Label_Entry;
   begin
      for Index in Block.First_Goto + 1 .. Natural (Label_Arrays.Length (State.Gotos)) loop
         pragma Loop_Invariant
           (Label_Arrays.Length (State.Gotos) = Label_Arrays.Length (State.Gotos)'Loop_Entry);
         Item := Label_Arrays.Element (State.Gotos, Work_Position (Index));
         if Register_Level (State, Item.Active) > Register_Level (State, Block.Active) then
            Item.Close := Item.Close or else Block.Has_Upvalue;
         end if;
         Item.Active := Block.Active;
         Label_Arrays.Replace_Element (State.Gotos, Work_Position (Index), Item);
      end loop;
   end Move_Gotos_Out;

   procedure Leave_Block (State : in out Compiler_State) is
      Position    : constant Natural := Block_Position (State, Depth (State));
      Block       : constant Block_Entry := Block_At (State, Position);
      Stack_Level : constant Natural := Register_Level (State, Block.Active);
      Has_Close   : Boolean := False;
      Has_Outer   : constant Boolean := Position > Current (State).Block_Base + 1;
      Item        : Function_Entry;
      Ignored     : Natural;
   begin
      if Position <= Current (State).Block_Base then
         Fail (State);
         return;
      end if;
      Remove_Variables (State, Block.Active);
      if Block.Is_Loop then
         Create_Label (State, State.Break_Name, 1, False, Has_Close);
      end if;
      if not Has_Close and then Has_Outer and then Block.Has_Upvalue then
         Code_ABC (State, Close, Stack_Level, 0, 0, False, Ignored);
      end if;
      Item := Current (State);
      Item.Free_Register := Stack_Level;
      Set_Current (State, Item);
      if Block.First_Label <= Natural (Label_Arrays.Length (State.Labels)) then
         Label_Arrays.Truncate (State.Labels, Label_Arrays.Extended_Index (Block.First_Label));
      end if;
      if Position = Natural (Block_Arrays.Length (State.Blocks)) then
         Block_Arrays.Truncate (State.Blocks, Block_Arrays.Length (State.Blocks) - 1);
      else
         Fail (State);
         return;
      end if;
      if Has_Outer then
         Move_Gotos_Out (State, Block);
      elsif Block.First_Goto < Natural (Label_Arrays.Length (State.Gotos))
        and then not State.Partial
      then
         --  The resolver reports undefined gotos; in a chunk without errors there are none.
         Fail (State);
      end if;
   end Leave_Block;

   procedure Open_Function (State : in out Compiler_State; Line : Natural) is
      Level   : Natural;
      Success : Boolean;
   begin
      if Depth (State) >= 2 ** 16 then
         Fail (State);
         return;
      end if;
      --  [puc lparser.c:addprototype] A nested function takes the next place among the
      --  functions of the enclosing one (its earlier ones are closed and counted there).
      if Depth (State) > 0
        and then Natural (Child_Arrays.Length (State.Children)) >= Current (State).Child_Base
        and then Natural (Child_Arrays.Length (State.Children)) - Current (State).Child_Base
                 >= Maximum_Functions
      then
         Raise_Error (State, Too_Many_Functions, 0);
         return;
      end if;
      Level := Depth (State) + 1;
      if Level > 2 ** 16
        or else Natural (Upvalue_Arrays.Length (State.Upvalues))
                  /= (Level - 1) * Maximum_Upvalues
      then
         Fail (State);
         return;
      end if;
      for Count in 1 .. Maximum_Upvalues loop
         Upvalue_Arrays.Append (State.Upvalues, (others => <>), State.Budget, Success);
         exit when not Success;
      end loop;
      if Success then
         Function_Arrays.Append
           (State.Functions,
            (Code_Base     => Natural (Instruction_Arrays.Length (State.Code)),
             Constant_Base => Natural (Constant_Arrays.Length (State.Constants)),
             Debug_Base    => Natural (Debug_Arrays.Length (State.Debug_Locals)),
             Child_Base    => Natural (Child_Arrays.Length (State.Children)),
             Upvalue_Count => 0,
             First_Local   => State.Variable_Count,
             First_Label   => Natural (Label_Arrays.Length (State.Labels)),
             Active        => 0,
             Free_Register => 0,
             Last_Target   => 0,
             Block_Base    => Natural (Block_Arrays.Length (State.Blocks)),
             Needs_Close   => False,
             Facts         => (Line_Defined => Line, others => <>)),
            State.Budget, Success);
      end if;
      if not Success then
         Raise_Error (State, Not_Enough_Memory, 0);
         return;
      end if;
      Enter_Block (State, False);
   end Open_Function;

   procedure Close_Function
     (State : in out Compiler_State; Result : in out Chunk; Last_Line : Natural)
   is
      Item    : Function_Entry;
      Level   : constant Natural := Depth (State);
      Success : Boolean := True;
      Facts   : Prototype_Header;
      Upvalue : Upvalue_Entry;
   begin
      Return_Values (State, Variables_On_Stack (State), 0);
      Leave_Block (State);
      Finish (State);
      Item := Current (State);
      if State.Failed then
         return;
      end if;
      if Item.Code_Base > Natural (Instruction_Arrays.Length (State.Code))
        or else Instruction_Arrays.Length (State.Code) /= Line_Arrays.Length (State.Lines)
        or else Item.Constant_Base > Natural (Constant_Arrays.Length (State.Constants))
        or else Item.Debug_Base > Natural (Debug_Arrays.Length (State.Debug_Locals))
        or else Item.Child_Base > Natural (Child_Arrays.Length (State.Children))
        or else Level = 0
        or else Level > 2 ** 16
        or else Natural (Upvalue_Arrays.Length (State.Upvalues)) /= Level * Maximum_Upvalues
        or else Item.Upvalue_Count > Maximum_Upvalues
      then
         Fail (State);
         return;
      end if;
      pragma Assert (Is_Well_Formed (Result));
      for Position in Item.Code_Base + 1 .. Natural (Instruction_Arrays.Length (State.Code)) loop
         pragma Loop_Invariant (Is_Well_Formed (Result));
         Append_Instruction
           (Result, State.Budget,
            Instruction_Arrays.Element (State.Code, Work_Position (Position)),
            Line_Arrays.Element (State.Lines, Work_Position (Position)), Success);
         exit when not Success;
      end loop;
      if Success then
         for Position in Item.Constant_Base + 1
                         .. Natural (Constant_Arrays.Length (State.Constants))
         loop
            pragma Loop_Invariant (Is_Well_Formed (Result));
            Append_Constant
              (Result, State.Budget,
               Constant_Arrays.Element (State.Constants, Work_Position (Position)), Success);
            exit when not Success;
         end loop;
      end if;
      if Success then
         for Index in 0 .. Item.Upvalue_Count - 1 loop
            pragma Loop_Invariant (Is_Well_Formed (Result));
            Upvalue := Upvalue_At (State, Level, Index);
            Append_Upvalue
              (Result, State.Budget,
               (Name     => Upvalue.Name,
                In_Stack => Upvalue.In_Stack,
                Index    => Bytecode.Byte (Natural'Min (Upvalue.Index, 255))),
               Success);
            exit when not Success;
         end loop;
      end if;
      if Success then
         for Position in Item.Debug_Base + 1
                         .. Natural (Debug_Arrays.Length (State.Debug_Locals))
         loop
            pragma Loop_Invariant (Is_Well_Formed (Result));
            Append_Local
              (Result, State.Budget,
               Debug_Arrays.Element (State.Debug_Locals, Work_Position (Position)), Success);
            exit when not Success;
         end loop;
      end if;
      if Success then
         for Position in Item.Child_Base + 1 .. Natural (Child_Arrays.Length (State.Children))
         loop
            pragma Loop_Invariant (Is_Well_Formed (Result));
            declare
               Child : constant Prototype_Index :=
                 Child_Arrays.Element (State.Children, Work_Position (Position));
            begin
               if Child not in 1 .. Prototype_Count (Result) then
                  Fail (State);
                  return;
               end if;
               Append_Child (Result, State.Budget, Child, Success);
            end;
            exit when not Success;
         end loop;
      end if;
      if Success then
         Facts := Item.Facts;
         Facts.Last_Line_Defined := Last_Line;
         Finish_Prototype (Result, State.Budget, Facts, Success);
      end if;
      if not Success then
         Raise_Error (State, Not_Enough_Memory, 0);
         return;
      end if;
      Instruction_Arrays.Truncate
        (State.Code, Instruction_Arrays.Extended_Index (Item.Code_Base));
      Line_Arrays.Truncate (State.Lines, Line_Arrays.Extended_Index (Item.Code_Base));
      if Natural (Constant_Arrays.Length (State.Constants)) >= Item.Constant_Base then
         Constant_Arrays.Truncate
           (State.Constants, Constant_Arrays.Extended_Index (Item.Constant_Base));
      end if;
      if Natural (Debug_Arrays.Length (State.Debug_Locals)) >= Item.Debug_Base then
         Debug_Arrays.Truncate
           (State.Debug_Locals, Debug_Arrays.Extended_Index (Item.Debug_Base));
      end if;
      if Natural (Child_Arrays.Length (State.Children)) >= Item.Child_Base then
         Child_Arrays.Truncate (State.Children, Child_Arrays.Extended_Index (Item.Child_Base));
      end if;
      if Natural (Upvalue_Arrays.Length (State.Upvalues)) >= (Level - 1) * Maximum_Upvalues then
         Upvalue_Arrays.Truncate
           (State.Upvalues, Upvalue_Arrays.Extended_Index ((Level - 1) * Maximum_Upvalues));
      end if;
      if Function_Arrays.Length (State.Functions) > 0 then
         Function_Arrays.Truncate
           (State.Functions, Function_Arrays.Length (State.Functions) - 1);
      end if;
      if Level > 1 then
         Child_Arrays.Append
           (State.Children, Prototype_Count (Result), State.Budget, Success);
         if not Success then
            Raise_Error (State, Not_Enough_Memory, 0);
         end if;
      end if;
   end Close_Function;

   procedure New_Local (State : in out Compiler_State; Name : Symbol_Index; Index : out Natural)
   is
      Item    : constant Function_Entry := Current (State);
      Success : Boolean := True;
   begin
      Index := 0;
      if State.Variable_Count < Item.First_Local then
         Fail (State);
         return;
      end if;
      if State.Variable_Count + 1 - Item.First_Local > Maximum_Variables then
         Raise_Error (State, Too_Many_Local_Variables, Item.Facts.Line_Defined);
         return;
      end if;
      if State.Variable_Count < Natural (Variable_Arrays.Length (State.Variables)) then
         Variable_Arrays.Replace_Element
           (State.Variables, Work_Position (State.Variable_Count + 1),
            (Name => Name, others => <>));
      elsif Variable_Arrays.Length (State.Variables) < Work_Position'Last then
         Variable_Arrays.Append
           (State.Variables, (Name => Name, others => <>), State.Budget, Success);
      else
         Success := False;
      end if;
      if not Success then
         Raise_Error (State, Not_Enough_Memory, 0);
         return;
      end if;
      if State.Variable_Count = Bounded_Count'Last then
         Fail (State);
         return;
      end if;
      State.Variable_Count := State.Variable_Count + 1;
      Index := State.Variable_Count - 1 - Item.First_Local;
   end New_Local;

   procedure Set_Variable
     (State : in out Compiler_State; Index : Natural; Kind : Variable_Kind;
      Value : Constant_Value)
   is
      Position : Natural;
      Item     : Variable_Entry;
   begin
      if Index > Maximum_Variables then
         Fail (State);
         return;
      end if;
      Position := Current (State).First_Local + Index;
      if Position >= Natural (Variable_Arrays.Length (State.Variables)) then
         Fail (State);
         return;
      end if;
      Item := Variable_Arrays.Element (State.Variables, Work_Position (Position + 1));
      Item.Kind := Kind;
      Item.Value := Value;
      Variable_Arrays.Replace_Element (State.Variables, Work_Position (Position + 1), Item);
   end Set_Variable;

   procedure Adjust_Locals (State : in out Compiler_State; Count : Natural) is
      Level    : Natural := Variables_On_Stack (State);
      Item     : Function_Entry;
      Position : Natural;
      Variable : Variable_Entry;
      Success  : Boolean;
   begin
      for Step in 1 .. Count loop
         Item := Current (State);
         Position := Item.First_Local + Item.Active;
         if Position >= Natural (Variable_Arrays.Length (State.Variables))
           or else Level > 255
           or else Item.Active = Bounded_Count'Last
           or else Debug_Arrays.Length (State.Debug_Locals) = Work_Position'Last
           or else Item.Debug_Base > Natural (Debug_Arrays.Length (State.Debug_Locals))
         then
            Fail (State);
            return;
         end if;
         if Natural (Debug_Arrays.Length (State.Debug_Locals)) - Item.Debug_Base
           >= Maximum_Debug_Locals
         then
            Raise_Error (State, Too_Many_Debug_Locals, 0);
            return;
         end if;
         Variable := Variable_Arrays.Element (State.Variables, Work_Position (Position + 1));
         Variable.Register := Level;
         Level := Level + 1;
         --  [puc lparser.c:registerlocalvar]
         Variable.Debug_Index :=
           Natural (Debug_Arrays.Length (State.Debug_Locals)) - Item.Debug_Base;
         Variable_Arrays.Replace_Element (State.Variables, Work_Position (Position + 1), Variable);
         Debug_Arrays.Append
           (State.Debug_Locals,
            (Name => Variable.Name, Start_PC => Natural'Min (PC (State), Entry_Count'Last),
             End_PC => 0),
            State.Budget, Success);
         if not Success then
            Raise_Error (State, Not_Enough_Memory, 0);
            return;
         end if;
         Item.Active := Item.Active + 1;
         Set_Current (State, Item);
      end loop;
   end Adjust_Locals;

   procedure Activate_Constant (State : in out Compiler_State) is
      Item : Function_Entry := Current (State);
   begin
      if Item.Active >= Maximum_Variables then
         Fail (State);
         return;
      end if;
      Item.Active := Item.Active + 1;
      Set_Current (State, Item);
   end Activate_Constant;

   --  [puc lparser.c:searchvar] Looks for an active variable Name of the function at Level.
   procedure Search_Variable
     (State : Compiler_State; Level : Natural; Name : Symbol_Index; Item : out Expression;
      Found : out Boolean)
   is
      Owner : constant Function_Entry := Function_At (State, Level);
      Entry_Item : Variable_Entry;
   begin
      Item := Make (Void);
      Found := False;
      for Index in reverse 0 .. Owner.Active - 1 loop
         Entry_Item := Variable (State, Owner.First_Local + Index);
         if Entry_Item.Name = Name then
            Found := True;
            if Entry_Item.Kind = Compile_Time_Variable then
               Item := Make (Compile_Time_Constant, Owner.First_Local + Index);
            else
               Item := (Kind => Local_Register, Variable => Index,
                        Register => Entry_Item.Register, others => <>);
            end if;
            return;
         end if;
      end loop;
   end Search_Variable;

   --  [puc lparser.c:searchupvalue] The upvalue Name of the function at Level, or -1.
   function Search_Upvalue
     (State : Compiler_State; Level : Natural; Name : Symbol_Index) return Integer
   is
   begin
      for Index in 0 .. Natural'Min (Function_At (State, Level).Upvalue_Count, Maximum_Upvalues)
                        - 1
      loop
         if Upvalue_At (State, Level, Index).Name = Name then
            return Index;
         end if;
      end loop;
      return -1;
   end Search_Upvalue;

   --  [puc lparser.c:markupval] Marks the block of the function at Level where variable
   --  Variable_Level is declared as having an upvalue.
   procedure Mark_Upvalue (State : in out Compiler_State; Level, Variable_Level : Natural) is
      Owner    : Function_Entry := Function_At (State, Level);
      Position : Natural := Block_Position (State, Level);
      Block    : Block_Entry;
   begin
      while Position > Owner.Block_Base + 1
        and then Block_At (State, Position).Active > Variable_Level
      loop
         pragma Loop_Variant (Decreases => Position);
         Position := Position - 1;
      end loop;
      Block := Block_At (State, Position);
      Block.Has_Upvalue := True;
      Set_Block_At (State, Position, Block);
      Owner.Needs_Close := True;
      Set_Function_At (State, Level, Owner);
   end Mark_Upvalue;

   procedure Mark_To_Be_Closed (State : in out Compiler_State) is
      Position : constant Natural := Block_Position (State, Depth (State));
      Block    : Block_Entry := Block_At (State, Position);
      Item     : Function_Entry := Current (State);
   begin
      Block.Has_Upvalue := True;
      Block.Inside_To_Be_Closed := True;
      Set_Block_At (State, Position, Block);
      Item.Needs_Close := True;
      Set_Current (State, Item);
   end Mark_To_Be_Closed;

   --  [puc lparser.c:newupvalue] Adds upvalue Name to the function at Level, captured from
   --  From (an expression of the function at Level - 1).
   procedure New_Upvalue
     (State : in out Compiler_State; Level : Natural; Name : Symbol_Index; From : Expression;
      Index : out Natural)
   is
      Owner    : Function_Entry := Function_At (State, Level);
      Position : Natural;
      Item     : Upvalue_Entry;
   begin
      Index := 0;
      if Level < 2 or else From.Register > 255 or else From.Info > 255
        or else From.Variable > Maximum_Variables
      then
         Fail (State);
         return;
      end if;
      if Owner.Upvalue_Count + 1 > Maximum_Upvalues then
         Raise_Error (State, Too_Many_Upvalues, Owner.Facts.Line_Defined);
         return;
      end if;
      if From.Kind = Local_Register then
         Item := (Name => Name, In_Stack => True, Index => From.Register,
                  Kind => Variable (State, Function_At (State, Level - 1).First_Local
                                           + From.Variable).Kind);
      else
         Item := (Name => Name, In_Stack => False, Index => From.Info,
                  Kind => Upvalue_At (State, Level - 1, From.Info).Kind);
      end if;
      Position := Upvalue_Position (Level, Owner.Upvalue_Count);
      if Position not in 1 .. Natural (Upvalue_Arrays.Length (State.Upvalues)) then
         Fail (State);
         return;
      end if;
      Upvalue_Arrays.Replace_Element (State.Upvalues, Work_Position (Position), Item);
      Index := Owner.Upvalue_Count;
      Owner.Upvalue_Count := Owner.Upvalue_Count + 1;
      Set_Function_At (State, Level, Owner);
   end New_Upvalue;

   --  [puc lparser.c:singlevaraux] for the open function (base 1), without recursion: finds
   --  the level where Name is a variable or an existing upvalue, then adds an upvalue to each
   --  function between there and the open one.
   procedure Single_Variable_Auxiliary
     (State : in out Compiler_State; Name : Symbol_Index; Item : out Expression)
   is
      Top   : constant Natural := Depth (State);
      Level : Natural := Top;
      Found : Boolean := False;
      Index : Integer;
      New_Index : Natural;
   begin
      Item := Make (Void);
      while Level > 0 loop
         pragma Loop_Variant (Decreases => Level);
         pragma Loop_Invariant (Level <= Top);
         Search_Variable (State, Level, Name, Item, Found);
         if Found then
            if Item.Kind = Local_Register and then Level < Top then
               Mark_Upvalue (State, Level, Item.Variable);
            end if;
            exit;
         end if;
         Index := Search_Upvalue (State, Level, Name);
         if Index >= 0 then
            Item := Make (Upvalue_Slot, Index);
            Found := True;
            exit;
         end if;
         Level := Level - 1;
      end loop;
      if not Found then
         Item := Make (Void);
         return;
      end if;
      --  The functions inside the level where the name was found capture it in turn.
      for Inner in Level + 1 .. Top loop
         exit when Item.Kind not in Local_Register | Upvalue_Slot;
         New_Upvalue (State, Inner, Name, Item, New_Index);
         exit when State.Failed;
         Item := Make (Upvalue_Slot, New_Index);
      end loop;
   end Single_Variable_Auxiliary;

   procedure Single_Variable
     (State : in out Compiler_State; Name : Symbol_Index; Name_Short : Boolean;
      Item : out Expression)
   is
      Key : Expression;
   begin
      Single_Variable_Auxiliary (State, Name, Item);
      if Item.Kind = Void then
         Single_Variable_Auxiliary (State, State.Environment_Name, Item);
         if Item.Kind = Void then
            Fail (State);
            return;
         end if;
         To_Any_Register_Or_Upvalue (State, Item);
         Key := (Kind => String_Value, String_Symbol => Name, String_Short => Name_Short,
                 others => <>);
         Indexed (State, Item, Key);
      end if;
   end Single_Variable;

   procedure Set_Vararg (State : in out Compiler_State; Parameters : Natural) is
      Item    : Function_Entry := Current (State);
      Ignored : Natural;
   begin
      Item.Facts.Is_Vararg := True;
      Set_Current (State, Item);
      Code_ABC (State, Vararg_Prepare, Parameters, 0, 0, False, Ignored);
   end Set_Vararg;

   procedure New_Goto
     (State : in out Compiler_State; Name : Symbol_Index; Line : Line_Number; PC : Jump_List)
   is
      Success : Boolean;
   begin
      if Label_Arrays.Length (State.Gotos) >= Maximum_Labels then
         Raise_Error (State, Too_Many_Labels, 0);
         return;
      end if;
      Label_Arrays.Append
        (State.Gotos,
         (Name => Name, Line => Line, Active => Current (State).Active, Close => False,
          PC => PC),
         State.Budget, Success);
      if not Success then
         Raise_Error (State, Not_Enough_Memory, 0);
      end if;
   end New_Goto;

   procedure Find_Label
     (State : Compiler_State; Name : Symbol_Index; Label : out Label_Entry; Found : out Boolean)
   is
   begin
      Label := (others => <>);
      Found := False;
      for Position in Current (State).First_Label + 1
                      .. Natural (Label_Arrays.Length (State.Labels))
      loop
         if Label_Arrays.Element (State.Labels, Work_Position (Position)).Name = Name then
            Label := Label_Arrays.Element (State.Labels, Work_Position (Position));
            Found := True;
            return;
         end if;
      end loop;
   end Find_Label;

end Pyro.Compiler.Code.Scopes;
