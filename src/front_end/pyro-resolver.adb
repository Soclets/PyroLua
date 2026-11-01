--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  Scope analysis: binds every name to its declaration and reports the errors PUC Lua finds
--  through scopes (const assignment, goto and labels, break).

with Pyro.Resolver.Variable_Arrays;
with Pyro.Resolver.Function_Arrays;
with Pyro.Resolver.Block_Arrays;
with Pyro.Resolver.Jump_Arrays;
with Pyro.Resolver.Frame_Arrays;
with Pyro.Diagnostics; use Pyro.Diagnostics;
with Pyro.Tokens;      use Pyro.Tokens;

package body Pyro.Resolver with SPARK_Mode => On is

   --  The bookkeeping mirrors lparser.c: active variables (Dyndata.actvar), labels and pending
   --  gotos (Dyndata.label, Dyndata.gt), blocks (BlockCnt) and functions (FuncState).

   type Walker is limited record
      Variables : Variable_Arrays.Growable_Array;
      Functions : Function_Arrays.Growable_Array;
      Blocks    : Block_Arrays.Growable_Array;
      Labels    : Jump_Arrays.Growable_Array;
      Gotos     : Jump_Arrays.Growable_Array;
      Frames    : Frame_Arrays.Growable_Array;
      Self_Name : Symbol_Index := No_Symbol;
      --  Memory ran out: the walk ends.
      Stopped   : Boolean := False;
   end record;

   --  The number of variables active in the current function (lparser.c's nactvar).
   function Variable_Count (W : Walker) return Entry_Index
   is (Variable_Arrays.Length (W.Variables));

   function Span_Of (Tree : Syntax_Tree; Index : Node_Index) return Span
   is (if Index in 1 .. Node_Count (Tree)
       then (First => Get (Tree, Index).First, Last => Get (Tree, Index).Last)
       else (First => 1, Last => 0));

   procedure Report
     (Stopped  : in out Boolean;
      Budget   : in out Memory_Budget;
      Problems : in out Diagnostic_Lists.Growable_Array;
      Item     : Diagnostic)
   with Post => Limit (Budget) = Limit (Budget)'Old and then (if Stopped'Old then Stopped)
   is
      Success : Boolean;
   begin
      Diagnostic_Lists.Append (Problems, Item, Budget, Success);
      if not Success then
         Stopped := True;
      end if;
   end Report;

   --  [puc lparser.c:new_localvar, adjustlocalvars] Activates a variable.
   procedure Declare_Variable
     (W           : in out Walker;
      Budget      : in out Memory_Budget;
      Name        : Symbol_Index;
      Attribute   : Attribute_Kind;
      Declaration : Node_Index)
   with Post => Limit (Budget) = Limit (Budget)'Old
   is
      Success : Boolean;
   begin
      Variable_Arrays.Append
        (W.Variables,
         (Name => Name, Attribute => Attribute, Declaration => Declaration,
          Owner => Function_Arrays.Length (W.Functions)),
         Budget, Success);
      if not Success then
         W.Stopped := True;
      end if;
   end Declare_Variable;

   --  [puc lparser.c:enterblock]
   procedure Enter_Block (W : in out Walker; Budget : in out Memory_Budget; Is_Loop : Boolean)
   with Post => Limit (Budget) = Limit (Budget)'Old
   is
      Success : Boolean;
   begin
      Block_Arrays.Append
        (W.Blocks,
         (Active      => Variable_Count (W),
          First_Label => Jump_Arrays.Length (W.Labels),
          First_Goto  => Jump_Arrays.Length (W.Gotos),
          Is_Loop     => Is_Loop),
         Budget, Success);
      if not Success then
         W.Stopped := True;
      end if;
   end Enter_Block;

   --  Removes pending goto Position, keeping the others in order.
   procedure Remove_Goto (Gotos : in out Jump_Arrays.Growable_Array; Position : Entry_Index)
   with
     Pre  => Position in 1 .. Jump_Arrays.Length (Gotos),
     Post => Jump_Arrays.Length (Gotos) = Jump_Arrays.Length (Gotos)'Old - 1
   is
      Last : constant Entry_Index := Jump_Arrays.Length (Gotos);
   begin
      for Index in Position .. Last - 1 loop
         pragma Loop_Invariant (Jump_Arrays.Length (Gotos) = Last);
         Jump_Arrays.Replace_Element (Gotos, Index, Jump_Arrays.Element (Gotos, Index + 1));
      end loop;
      Jump_Arrays.Truncate (Gotos, Last - 1);
   end Remove_Goto;

   --  [puc lparser.c:leaveblock] Closes the innermost block: its variables and labels go,
   --  a loop resolves its breaks, and its pending gotos move out to the enclosing block, or,
   --  at the end of a function, are reported as undefined.
   procedure Leave_Block
     (W        : in out Walker;
      Tree     : Syntax_Tree;
      Budget   : in out Memory_Budget;
      Problems : in out Diagnostic_Lists.Growable_Array)
   with
     Pre  => Is_Well_Formed (Tree),
     Post => Limit (Budget) = Limit (Budget)'Old
   is
      Blocks : constant Entry_Index := Block_Arrays.Length (W.Blocks);
      Closed : Block_Entry;
      Owner  : Function_Entry;
      Index  : Entry_Index'Base;
      Body_Node : Node;
   begin
      if Blocks = 0 then
         return;
      end if;
      Closed := Block_Arrays.Element (W.Blocks, Blocks);
      if Closed.Active <= Variable_Count (W) then
         Variable_Arrays.Truncate (W.Variables, Closed.Active);
      end if;
      if Closed.First_Goto <= Jump_Arrays.Length (W.Gotos) then
         --  [puc lparser.c:createlabel] A loop's "break" label resolves its breaks.
         if Closed.Is_Loop then
            Index := Entry_Index'Base (Closed.First_Goto) + 1;
            for Step in 1 .. Jump_Arrays.Length (W.Gotos) loop
               pragma Loop_Invariant (Index >= 1 and then Index <= Entry_Index'Last + 1);
               pragma Loop_Invariant (Limit (Budget) = Limit (Budget)'Loop_Entry);
               pragma Loop_Invariant (Block_Arrays.Length (W.Blocks) = Blocks);
               exit when Index > Jump_Arrays.Length (W.Gotos);
               if Jump_Arrays.Element (W.Gotos, Index).Is_Break then
                  Remove_Goto (W.Gotos, Index);
               else
                  Index := Index + 1;
               end if;
            end loop;
         end if;
      end if;
      if Closed.First_Label <= Jump_Arrays.Length (W.Labels) then
         Jump_Arrays.Truncate (W.Labels, Closed.First_Label);
      end if;
      pragma Assert (Block_Arrays.Length (W.Blocks) = Blocks);
      Block_Arrays.Truncate (W.Blocks, Blocks - 1);
      if Function_Arrays.Length (W.Functions) = 0
        or else Closed.First_Goto > Jump_Arrays.Length (W.Gotos)
      then
         return;
      end if;
      Owner := Function_Arrays.Element (W.Functions, Function_Arrays.Length (W.Functions));
      if Blocks - 1 > Owner.Block_Base then
         --  [puc lparser.c:movegotosout]
         for Position in Closed.First_Goto + 1 .. Jump_Arrays.Length (W.Gotos) loop
            pragma Loop_Invariant
              (Jump_Arrays.Length (W.Gotos) = Jump_Arrays.Length (W.Gotos)'Loop_Entry);
            declare
               Pending : Jump_Entry := Jump_Arrays.Element (W.Gotos, Position);
            begin
               Pending.Active := Closed.Active;
               Jump_Arrays.Replace_Element (W.Gotos, Position, Pending);
            end;
         end loop;
         return;
      end if;
      --  [puc lparser.c:undefgoto] The function ends with these gotos pending.
      if Owner.Body_Node not in 1 .. Node_Count (Tree) then
         return;
      end if;
      Body_Node := Get (Tree, Owner.Body_Node);
      for Position in Closed.First_Goto + 1 .. Jump_Arrays.Length (W.Gotos) loop
         pragma Loop_Invariant
           (Jump_Arrays.Length (W.Gotos) = Jump_Arrays.Length (W.Gotos)'Loop_Entry);
         pragma Loop_Invariant (Limit (Budget) = Limit (Budget)'Loop_Entry);
         declare
            Pending : constant Jump_Entry := Jump_Arrays.Element (W.Gotos, Position);
            Item    : Diagnostic;
         begin
            --  In a function cut short, a goto's label could be in the missing part; a break
            --  outside every loop is an error whatever follows.
            if Pending.Is_Break or else not Body_Node.Is_Incomplete then
               Item.What := (if Pending.Is_Break then Break_Outside_Loop else No_Visible_Label);
               Item.Name := Pending.Name;
               Item.Has_Place := True;
               Item.Place := Span_Of (Tree, Pending.Node);
               Item.Has_Lua_Line := True;
               Item.Lua_Line := Body_Node.Check_Line;
               Item.Other_Line := Pending.Line;
               Item.Detection :=
                 (if Body_Node.Is_Incomplete then (Ordinal => Token_Ordinal'Last, During => Parsing)
                  else Body_Node.Check_Point);
               Report (W.Stopped, Budget, Problems, Item);
            end if;
         end;
      end loop;
      if Closed.First_Goto <= Jump_Arrays.Length (W.Gotos) then
         Jump_Arrays.Truncate (W.Gotos, Closed.First_Goto);
      end if;
   end Leave_Block;

   --  [puc lparser.c:searchvar, singlevaraux] The innermost active variable named Name, or 0.
   function Find_Variable (W : Walker; Name : Symbol_Index) return Entry_Index
   with Post => Find_Variable'Result <= Variable_Count (W)
   is
   begin
      if Name = No_Symbol then
         return 0;
      end if;
      for Index in reverse 1 .. Variable_Count (W) loop
         if Variable_Arrays.Element (W.Variables, Index).Name = Name then
            return Index;
         end if;
      end loop;
      return 0;
   end Find_Variable;

   --  [puc lparser.c:singlevar] Binds a Name_Expression.
   procedure Bind
     (W        : Walker;
      Tree     : Syntax_Tree;
      Index    : Node_Index;
      Bindings : in out Binding_Table)
   with Pre => Is_Well_Formed (Tree) and then Index in 1 .. Node_Count (Tree)
   is
      Found  : constant Entry_Index := Find_Variable (W, Get (Tree, Index).Symbol);
      Result : Binding := (Kind => Global, Declaration => No_Node);
   begin
      if Found /= 0 then
         declare
            Variable : constant Variable_Entry := Variable_Arrays.Element (W.Variables, Found);
         begin
            Result :=
              (Kind        => (if Variable.Owner = Function_Arrays.Length (W.Functions)
                               then Local_Variable else Upvalue),
               Declaration => Variable.Declaration);
         end;
      end if;
      if Index <= Binding_Arrays.Length (Bindings.Items) then
         Binding_Arrays.Replace_Element (Bindings.Items, Index, Result);
      end if;
   end Bind;

   --  [puc lparser.c:check_readonly] Reports an assignment to a <const> or <close> variable.
   --  Target is the assigned expression; Checker is the node that records when PUC checks.
   procedure Check_Assignable
     (W        : in out Walker;
      Tree     : Syntax_Tree;
      Target   : Node_Index;
      Checker  : Node_Index;
      Budget   : in out Memory_Budget;
      Problems : in out Diagnostic_Lists.Growable_Array)
   with
     Pre  => Is_Well_Formed (Tree) and then Checker in 1 .. Node_Count (Tree),
     Post => Limit (Budget) = Limit (Budget)'Old
   is
      Found : Entry_Index;
      Item  : Diagnostic;
   begin
      if Target not in 1 .. Node_Count (Tree) or else Get (Tree, Target).Kind /= Name_Expression
      then
         return;
      end if;
      Found := Find_Variable (W, Get (Tree, Target).Symbol);
      if Found = 0 then
         return;
      end if;
      declare
         Variable : constant Variable_Entry := Variable_Arrays.Element (W.Variables, Found);
      begin
         if Variable.Attribute = Regular then
            return;
         end if;
         Item.What := Assignment_To_Constant;
         Item.Name := Variable.Name;
         Item.Is_Close := Variable.Attribute = Close_Attribute;
         Item.Has_Place := True;
         Item.Place := Span_Of (Tree, Target);
         if Variable.Declaration /= No_Node then
            Item.Links := 1;
            Item.First_Link := Span_Of (Tree, Variable.Declaration);
         end if;
         Item.Has_Lua_Line := True;
         Item.Lua_Line := Get (Tree, Checker).Check_Line;
         Item.Detection := Get (Tree, Checker).Check_Point;
         Report (W.Stopped, Budget, Problems, Item);
      end;
   end Check_Assignable;

   --  [puc lparser.c:labelstat] Declares a label: checks for a visible label of the same name
   --  (checkrepeated), then resolves the pending gotos of the block that jump to it
   --  (createlabel, solvegotos), reporting a jump into the scope of a local.
   procedure Declare_Label
     (W        : in out Walker;
      Tree     : Syntax_Tree;
      Index    : Node_Index;
      Budget   : in out Memory_Budget;
      Problems : in out Diagnostic_Lists.Growable_Array)
   with
     Pre  => Is_Well_Formed (Tree) and then Index in 1 .. Node_Count (Tree),
     Post => Limit (Budget) = Limit (Budget)'Old
   is
      Label    : constant Node := Get (Tree, Index);
      Owner    : Function_Entry;
      Block    : Block_Entry;
      Created  : Jump_Entry;
      Success  : Boolean;
      Position : Entry_Index'Base;
      Item     : Diagnostic;
   begin
      if Function_Arrays.Length (W.Functions) = 0 or else Block_Arrays.Length (W.Blocks) = 0 then
         return;
      end if;
      Owner := Function_Arrays.Element (W.Functions, Function_Arrays.Length (W.Functions));
      Block := Block_Arrays.Element (W.Blocks, Block_Arrays.Length (W.Blocks));
      --  [puc lparser.c:checkrepeated] The labels of the function still visible.
      for Visible in Owner.First_Label + 1 .. Jump_Arrays.Length (W.Labels) loop
         pragma Loop_Invariant (Limit (Budget) = Limit (Budget)'Loop_Entry);
         declare
            Other : constant Jump_Entry := Jump_Arrays.Element (W.Labels, Visible);
         begin
            if Other.Name = Label.Symbol then
               Item.What := Label_Already_Defined;
               Item.Name := Label.Symbol;
               Item.Has_Place := True;
               Item.Place := (First => Label.First, Last => Label.Last);
               Item.Links := 1;
               Item.First_Link := Span_Of (Tree, Other.Node);
               Item.Has_Lua_Line := True;
               Item.Lua_Line := Label.Check_Line;
               Item.Other_Line := Other.Line;
               Item.Detection := Label.Check_Point;
               Report (W.Stopped, Budget, Problems, Item);
               exit;
            end if;
         end;
      end loop;
      --  [puc lparser.c:createlabel] A label last in its block counts as outside the scope of
      --  the block's locals.
      Created :=
        (Name     => Label.Symbol,
         Is_Break => False,
         Line     => Label.Line,
         Active   => (if Label.Is_Last_Label then Block.Active else Variable_Count (W)),
         Node     => Index);
      Jump_Arrays.Append (W.Labels, Created, Budget, Success);
      if not Success then
         W.Stopped := True;
         return;
      end if;
      --  [puc lparser.c:solvegotos]
      Position := Entry_Index'Base (Block.First_Goto) + 1;
      for Step in 1 .. Jump_Arrays.Length (W.Gotos) loop
         pragma Loop_Invariant (Position >= 1 and then Position <= Entry_Index'Last + 1);
         pragma Loop_Invariant (Limit (Budget) = Limit (Budget)'Loop_Entry);
         exit when Position > Jump_Arrays.Length (W.Gotos);
         declare
            Pending : constant Jump_Entry := Jump_Arrays.Element (W.Gotos, Position);
         begin
            if not Pending.Is_Break and then Pending.Name = Label.Symbol then
               if Pending.Active < Created.Active then
                  --  [puc lparser.c:jumpscopeerror] The first local whose scope it enters.
                  Item := (others => <>);
                  Item.What := Goto_Into_Scope;
                  Item.Name := Label.Symbol;
                  Item.Has_Place := True;
                  Item.Place := Span_Of (Tree, Pending.Node);
                  if Pending.Active + 1 <= Variable_Count (W) then
                     declare
                        Entered : constant Variable_Entry :=
                          Variable_Arrays.Element (W.Variables, Pending.Active + 1);
                     begin
                        Item.Other_Name := Entered.Name;
                        if Entered.Declaration /= No_Node then
                           Item.Links := 2;
                           Item.First_Link := Span_Of (Tree, Entered.Declaration);
                           Item.Second_Link := (First => Label.First, Last => Label.Last);
                        end if;
                     end;
                  end if;
                  Item.Has_Lua_Line := True;
                  Item.Lua_Line := Label.Check_Line;
                  Item.Other_Line := Pending.Line;
                  Item.Detection := Label.Check_Point;
                  Report (W.Stopped, Budget, Problems, Item);
               end if;
               Remove_Goto (W.Gotos, Position);
            else
               Position := Position + 1;
            end if;
         end;
      end loop;
   end Declare_Label;

   --  [puc lparser.c:gotostat, breakstat] A goto to a visible label is resolved at once
   --  (a backward jump); otherwise it waits for its label.
   procedure Declare_Goto
     (W      : in out Walker;
      Tree   : Syntax_Tree;
      Index  : Node_Index;
      Budget : in out Memory_Budget)
   with
     Pre  => Is_Well_Formed (Tree) and then Index in 1 .. Node_Count (Tree),
     Post => Limit (Budget) = Limit (Budget)'Old
   is
      Statement : constant Node := Get (Tree, Index);
      Is_Break  : constant Boolean := Statement.Kind = Break_Statement;
      Success   : Boolean;
   begin
      if not Is_Break and then Function_Arrays.Length (W.Functions) > 0 then
         --  [puc lparser.c:findlabel]
         for Visible in
           Function_Arrays.Element (W.Functions, Function_Arrays.Length (W.Functions)).First_Label
           + 1 .. Jump_Arrays.Length (W.Labels)
         loop
            if Jump_Arrays.Element (W.Labels, Visible).Name = Statement.Symbol then
               return;
            end if;
         end loop;
      end if;
      Jump_Arrays.Append
        (W.Gotos,
         (Name     => Statement.Symbol,
          Is_Break => Is_Break,
          Line     => Statement.Line,
          Active   => Variable_Count (W),
          Node     => Index),
         Budget, Success);
      if not Success then
         W.Stopped := True;
      end if;
   end Declare_Goto;

   --  Declares the names of a Name_List (or a single Local_Name).
   procedure Declare_Names
     (W      : in out Walker;
      Tree   : Syntax_Tree;
      Names  : Node_Index;
      Budget : in out Memory_Budget)
   with
     Pre  => Is_Well_Formed (Tree) and then Names <= Node_Count (Tree),
     Post => Limit (Budget) = Limit (Budget)'Old
   is
      Item : Node;
   begin
      if Names = No_Node then
         return;
      end if;
      Item := Get (Tree, Names);
      if Item.Kind = Local_Name then
         Declare_Variable (W, Budget, Item.Symbol, Item.Attribute, Names);
         return;
      end if;
      for Position in 1 .. Item.List_Length loop
         pragma Loop_Invariant (Limit (Budget) = Limit (Budget)'Loop_Entry);
         declare
            Name_Node : constant Node_Index := List_Item (Tree, Names, Position);
            Name_Item : constant Node := Get (Tree, Name_Node);
         begin
            Declare_Variable (W, Budget, Name_Item.Symbol, Name_Item.Attribute, Name_Node);
         end;
      end loop;
   end Declare_Names;

   --  Declares Count hidden variables (lparser.c's "(for state)").
   procedure Declare_Hidden (W : in out Walker; Budget : in out Memory_Budget; Count : Natural)
   with Post => Limit (Budget) = Limit (Budget)'Old
   is
   begin
      for Index in 1 .. Count loop
         pragma Loop_Invariant (Limit (Budget) = Limit (Budget)'Loop_Entry);
         Declare_Variable (W, Budget, No_Symbol, Regular, No_Node);
      end loop;
   end Declare_Hidden;

   --  Pushes Child (if it is a node) to be walked next.
   procedure Visit
     (W      : in out Walker;
      Tree   : Syntax_Tree;
      Child  : Node_Index;
      Budget : in out Memory_Budget;
      Scoped : Boolean := True)
   with
     Pre  => Is_Well_Formed (Tree),
     Post => Limit (Budget) = Limit (Budget)'Old
   is
      Success : Boolean;
   begin
      if Child /= No_Node and then Child <= Node_Count (Tree) then
         Frame_Arrays.Append
           (W.Frames, (Node => Child, Step => 0, Scoped => Scoped), Budget, Success);
         if not Success then
            W.Stopped := True;
         end if;
      end if;
   end Visit;

   --  The top frame moves to its next step.
   procedure Advance (W : in out Walker)
   with Post => Frame_Arrays.Length (W.Frames) = Frame_Arrays.Length (W.Frames)'Old
   is
      Top : constant Entry_Index := Frame_Arrays.Length (W.Frames);
   begin
      if Top > 0 then
         declare
            Current : Frame := Frame_Arrays.Element (W.Frames, Top);
         begin
            if Current.Step < Natural'Last then
               Current.Step := Current.Step + 1;
            end if;
            Frame_Arrays.Replace_Element (W.Frames, Top, Current);
         end;
      end if;
   end Advance;

   --  The top frame is done.
   procedure Finish (W : in out Walker) is
   begin
      if Frame_Arrays.Length (W.Frames) > 0 then
         Frame_Arrays.Truncate (W.Frames, Frame_Arrays.Length (W.Frames) - 1);
      end if;
   end Finish;

   --  One step of the walk of the top frame.
   procedure Step
     (W        : in out Walker;
      Tree     : Syntax_Tree;
      Budget   : in out Memory_Budget;
      Problems : in out Diagnostic_Lists.Growable_Array;
      Bindings : in out Binding_Table)
   with
     Pre  => Is_Well_Formed (Tree) and then Frame_Arrays.Length (W.Frames) > 0,
     Post => Limit (Budget) = Limit (Budget)'Old
   is
      Current : constant Frame := Frame_Arrays.Element (W.Frames, Frame_Arrays.Length (W.Frames));
      Index   : constant Node_Index := Current.Node;
      Item    : Node;
      Length  : Natural;
      At_Step : constant Natural := Current.Step;
      Success : Boolean;
   begin
      if Index not in 1 .. Node_Count (Tree) then
         Finish (W);
         return;
      end if;
      Item := Get (Tree, Index);
      Length := Natural (Item.List_Length);
      Advance (W);
      case Item.Kind is
         when Function_Body =>
            if At_Step = 0 then
               --  [puc lparser.c:open_func, body]
               Function_Arrays.Append
                 (W.Functions,
                  (First_Variable => Variable_Count (W),
                   First_Label    => Jump_Arrays.Length (W.Labels),
                   First_Goto     => Jump_Arrays.Length (W.Gotos),
                   Block_Base     => Block_Arrays.Length (W.Blocks),
                   Body_Node      => Index),
                  Budget, Success);
               if not Success then
                  W.Stopped := True;
                  return;
               end if;
               Enter_Block (W, Budget, Is_Loop => False);
               if Item.Is_Method then
                  Declare_Variable (W, Budget, W.Self_Name, Regular, No_Node);
               end if;
               Declare_Names (W, Tree, Child (Tree, Index, 1), Budget);
               Visit (W, Tree, Child (Tree, Index, 2), Budget, Scoped => False);
            else
               Leave_Block (W, Tree, Budget, Problems);
               if Function_Arrays.Length (W.Functions) > 0 then
                  Function_Arrays.Truncate (W.Functions, Function_Arrays.Length (W.Functions) - 1);
               end if;
               Finish (W);
            end if;
         when Block =>
            if At_Step = 0 then
               if Current.Scoped then
                  Enter_Block (W, Budget, Is_Loop => False);
               end if;
            elsif At_Step <= Length then
               Visit (W, Tree, List_Item (Tree, Index, List_Index (At_Step)), Budget);
            else
               if Current.Scoped then
                  Leave_Block (W, Tree, Budget, Problems);
               end if;
               Finish (W);
            end if;
         when Local_Statement =>
            if At_Step = 0 then
               Visit (W, Tree, Child (Tree, Index, 2), Budget);
            else
               Declare_Names (W, Tree, Child (Tree, Index, 1), Budget);
               Finish (W);
            end if;
         when Local_Function =>
            if At_Step = 0 then
               Declare_Names (W, Tree, Child (Tree, Index, 1), Budget);
               Visit (W, Tree, Child (Tree, Index, 2), Budget);
            else
               Finish (W);
            end if;
         when Assignment_Target =>
            if At_Step = 0 then
               Visit (W, Tree, Child (Tree, Index, 1), Budget);
            else
               Check_Assignable (W, Tree, Child (Tree, Index, 1), Index, Budget, Problems);
               Finish (W);
            end if;
         when Function_Statement =>
            if At_Step = 0 then
               Visit (W, Tree, Child (Tree, Index, 1), Budget);
            elsif At_Step = 1 then
               Visit (W, Tree, Child (Tree, Index, 2), Budget);
            else
               Check_Assignable (W, Tree, Child (Tree, Index, 1), Index, Budget, Problems);
               Finish (W);
            end if;
         when While_Statement =>
            if At_Step = 0 then
               Visit (W, Tree, Child (Tree, Index, 1), Budget);
            elsif At_Step = 1 then
               Enter_Block (W, Budget, Is_Loop => True);
               Visit (W, Tree, Child (Tree, Index, 2), Budget);
            else
               Leave_Block (W, Tree, Budget, Problems);
               Finish (W);
            end if;
         when Repeat_Statement =>
            --  [puc lparser.c:repeatstat] A loop block, and a scope block holding the body and
            --  the condition.
            if At_Step = 0 then
               Enter_Block (W, Budget, Is_Loop => True);
               Enter_Block (W, Budget, Is_Loop => False);
               Visit (W, Tree, Child (Tree, Index, 1), Budget, Scoped => False);
            elsif At_Step = 1 then
               Visit (W, Tree, Child (Tree, Index, 2), Budget);
            else
               Leave_Block (W, Tree, Budget, Problems);
               Leave_Block (W, Tree, Budget, Problems);
               Finish (W);
            end if;
         when If_Statement =>
            if At_Step < Length then
               Visit (W, Tree, List_Item (Tree, Index, List_Index (At_Step + 1)), Budget);
            elsif At_Step = Length then
               Visit (W, Tree, Child (Tree, Index, 1), Budget);
            else
               Finish (W);
            end if;
         when If_Clause =>
            if At_Step = 0 then
               Visit (W, Tree, Child (Tree, Index, 1), Budget);
            elsif At_Step = 1 then
               Visit (W, Tree, Child (Tree, Index, 2), Budget);
            else
               Finish (W);
            end if;
         when Numeric_For | Generic_For =>
            --  [puc lparser.c:forstat, fornum, forlist, forbody] A loop block with the hidden
            --  control variables, a block with the declared ones, and the body's own block.
            if At_Step = 0 then
               Enter_Block (W, Budget, Is_Loop => True);
               Visit (W, Tree, Child (Tree, Index, 2), Budget);
            elsif At_Step = 1 then
               Declare_Hidden (W, Budget, (if Item.Kind = Numeric_For then 3 else 4));
               Enter_Block (W, Budget, Is_Loop => False);
               Declare_Names (W, Tree, Child (Tree, Index, 1), Budget);
               Visit (W, Tree, Child (Tree, Index, 3), Budget);
            else
               Leave_Block (W, Tree, Budget, Problems);
               Leave_Block (W, Tree, Budget, Problems);
               Finish (W);
            end if;
         when Break_Statement | Goto_Statement =>
            Declare_Goto (W, Tree, Index, Budget);
            Finish (W);
         when Label_Statement =>
            --  The labels right after it are declared first, as PUC does.
            if At_Step < Length then
               Visit (W, Tree, List_Item (Tree, Index, List_Index (At_Step + 1)), Budget);
            else
               --  A label whose closing '::' is missing is no label PUC Lua would declare.
               if not Get (Tree, Index).Is_Incomplete then
                  Declare_Label (W, Tree, Index, Budget, Problems);
               end if;
               Finish (W);
            end if;
         when Name_Expression =>
            Bind (W, Tree, Index, Bindings);
            Finish (W);
         when others =>
            --  Every other node: its children, then its list, in order.
            if At_Step < 3 then
               Visit (W, Tree, Child (Tree, Index, Child_Slot (At_Step + 1)), Budget);
            elsif At_Step < 3 + Length then
               Visit (W, Tree, List_Item (Tree, Index, List_Index (At_Step - 2)), Budget);
            else
               Finish (W);
            end if;
      end case;
   end Step;

   procedure Resolve
     (Tree     : Syntax_Tree;
      Root     : Node_Index;
      Symbols  : Symbol_Table;
      Budget   : in out Memory_Budget;
      Problems : in out Diagnostic_Lists.Growable_Array;
      Bindings : in out Binding_Table)
   is
      W       : Walker;
      Success : Boolean;
   begin
      Binding_Arrays.Truncate (Bindings.Items, 0);
      for Index in 1 .. Node_Count (Tree) loop
         pragma Loop_Invariant (Limit (Budget) = Limit (Budget)'Loop_Entry);
         Binding_Arrays.Append (Bindings.Items, (others => <>), Budget, Success);
         exit when not Success;
      end loop;
      W.Self_Name := Find_Text (Symbols, "self");
      if Root /= No_Node then
         Visit (W, Tree, Root, Budget);
      end if;
      --  Each node is walked in at most a few steps per child and list item, so this bound is
      --  never reached on a tree; it only makes termination evident.
      for Iteration in 1 .. 8 * Natural (Node_Count (Tree)) + 8 loop
         pragma Loop_Invariant (Limit (Budget) = Limit (Budget)'Loop_Entry);
         exit when W.Stopped or else Frame_Arrays.Length (W.Frames) = 0;
         Step (W, Tree, Budget, Problems, Bindings);
      end loop;
      if W.Stopped then
         Report (W.Stopped, Budget, Problems, (What => Not_Enough_Memory, others => <>));
         pragma Assert (W.Stopped);
      end if;
      Variable_Arrays.Clear (W.Variables, Budget);
      Function_Arrays.Clear (W.Functions, Budget);
      Block_Arrays.Clear (W.Blocks, Budget);
      Jump_Arrays.Clear (W.Labels, Budget);
      Jump_Arrays.Clear (W.Gotos, Budget);
      Frame_Arrays.Clear (W.Frames, Budget);
      --  [proof] The walker's memory is released.
      pragma Assert
        (Variable_Arrays.Is_Released (W.Variables)
         and then Function_Arrays.Is_Released (W.Functions)
         and then Block_Arrays.Is_Released (W.Blocks)
         and then Jump_Arrays.Is_Released (W.Labels)
         and then Jump_Arrays.Is_Released (W.Gotos)
         and then Frame_Arrays.Is_Released (W.Frames));
   end Resolve;

   procedure Clear (Table : in out Binding_Table; Budget : in out Memory_Budget) is
   begin
      Binding_Arrays.Clear (Table.Items, Budget);
   end Clear;

end Pyro.Resolver;
