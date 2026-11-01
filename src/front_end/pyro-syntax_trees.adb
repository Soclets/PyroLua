--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  The syntax tree arena: nodes indexed by Node_Index, children always older than their parent.

with Pyro.Tokens; use Pyro.Tokens;

package body Pyro.Syntax_Trees with SPARK_Mode => On is

   use type Interfaces.Unsigned_64;

   --  The fields each kind keeps in its four slots. A node with another field that is not the
   --  default (or a field too large for its slot) is spilled.
   --
   --    Value_Layout   Integer_Literal, Float_Literal: Value (low half, high half)
   --    Method_Layout  Method_Call: child 1, Symbol, List_First, List_Length
   --    Check_Layout   Function_Body, Function_Statement, Assignment_Target: children 1 and 2,
   --                   the check ordinal and line (the check phase is in the header)
   --    Label_Layout   Label_Statement: Symbol, -, the check ordinal and line
   --    List_Layout    the kinds with a list: children 1 and 2, List_First, List_Length
   --    Child_Layout   the other kinds: children 1, 2 and 3, Symbol
   type Layout is
     (Value_Layout, Method_Layout, Check_Layout, Label_Layout, List_Layout, Child_Layout);

   function Layout_Of (Kind : Node_Kind) return Layout
   is (case Kind is
         when Integer_Literal | Float_Literal => Value_Layout,
         when Method_Call => Method_Layout,
         when Function_Body | Function_Statement | Assignment_Target => Check_Layout,
         when Label_Statement => Label_Layout,
         when Table_Constructor | Call_Expression | If_Statement | Block | Expression_List
            | Name_List => List_Layout,
         when others => Child_Layout);

   --  A slot read as each kind of field; a value out of the field's range reads as its default.
   function To_Node (Value : Slot_Value) return Node_Index
   is (if Value <= Slot_Value (Node_Index'Last) then Node_Index (Value) else No_Node);

   function To_List (Value : Slot_Value) return List_Index
   is (if Value <= Slot_Value (List_Index'Last) then List_Index (Value) else 0);

   function To_Symbol (Value : Slot_Value) return Symbol_Index
   is (if Value <= Slot_Value (Symbol_Index'Last) then Symbol_Index (Value) else No_Symbol);

   function To_Ordinal (Value : Slot_Value) return Token_Ordinal
   is (if Value <= Slot_Value (Token_Ordinal'Last) then Token_Ordinal (Value) else 0);

   function To_Line (Value : Slot_Value) return Line_Number
   is (if Value in 1 .. Slot_Value (Line_Number'Last) then Line_Number (Value) else 1);

   --  Item in the stored form of its kind, not spilled (it may not read back the same).
   function Encode (Item : Node) return Stored_Node
   with Post => not Encode'Result.Head.Spilled
   is
      Result : Stored_Node :=
        (Head   =>
           (Kind          => Item.Kind,
            Operator      => Item.Operator,
            Attribute     => Item.Attribute,
            Is_Vararg     => Item.Is_Vararg,
            Is_Method     => Item.Is_Method,
            Is_Name_Key   => Item.Is_Name_Key,
            Is_Incomplete => Item.Is_Incomplete,
            Is_Last_Label => Item.Is_Last_Label,
            During        => Item.Check_Point.During,
            Spilled       => False),
         First  => Item.First,
         Last   => Item.Last,
         Line   => Item.Line,
         others => 0);
   begin
      case Layout_Of (Item.Kind) is
         when Value_Layout =>
            Result.Slot_1 := Slot_Value (Item.Value mod 2 ** 32);
            Result.Slot_2 := Slot_Value (Item.Value / 2 ** 32);
         when Method_Layout =>
            Result.Slot_1 := Slot_Value (Item.First_Child);
            Result.Slot_2 := Slot_Value (Item.Symbol);
            Result.Slot_3 := Slot_Value (Item.List_First);
            Result.Slot_4 := Slot_Value (Item.List_Length);
         when Check_Layout =>
            Result.Slot_1 := Slot_Value (Item.First_Child);
            Result.Slot_2 := Slot_Value (Item.Second_Child);
            Result.Slot_3 := Slot_Value (Item.Check_Point.Ordinal);
            Result.Slot_4 := Slot_Value (Item.Check_Line);
         when Label_Layout =>
            Result.Slot_1 := Slot_Value (Item.Symbol);
            Result.Slot_3 := Slot_Value (Item.Check_Point.Ordinal);
            Result.Slot_4 := Slot_Value (Item.Check_Line);
         when List_Layout =>
            Result.Slot_1 := Slot_Value (Item.First_Child);
            Result.Slot_2 := Slot_Value (Item.Second_Child);
            Result.Slot_3 := Slot_Value (Item.List_First);
            Result.Slot_4 := Slot_Value (Item.List_Length);
         when Child_Layout =>
            Result.Slot_1 := Slot_Value (Item.First_Child);
            Result.Slot_2 := Slot_Value (Item.Second_Child);
            Result.Slot_3 := Slot_Value (Item.Third_Child);
            Result.Slot_4 := Slot_Value (Item.Symbol);
      end case;
      return Result;
   end Encode;

   --  The node Item stores in the form of its kind (whether or not it is spilled).
   function Decode (Item : Stored_Node) return Node
   is (Kind          => Item.Head.Kind,
       First         => Item.First,
       Last          => Item.Last,
       Line          => Item.Line,
       First_Child   =>
         (case Layout_Of (Item.Head.Kind) is
            when Method_Layout | Check_Layout | List_Layout | Child_Layout =>
              To_Node (Item.Slot_1),
            when Value_Layout | Label_Layout => No_Node),
       Second_Child  =>
         (case Layout_Of (Item.Head.Kind) is
            when Check_Layout | List_Layout | Child_Layout => To_Node (Item.Slot_2),
            when Value_Layout | Method_Layout | Label_Layout => No_Node),
       Third_Child   =>
         (if Layout_Of (Item.Head.Kind) = Child_Layout then To_Node (Item.Slot_3) else No_Node),
       List_First    =>
         (if Layout_Of (Item.Head.Kind) in Method_Layout | List_Layout
          then To_List (Item.Slot_3) else 0),
       List_Length   =>
         (if Layout_Of (Item.Head.Kind) in Method_Layout | List_Layout
          then To_List (Item.Slot_4) else 0),
       Symbol        =>
         (case Layout_Of (Item.Head.Kind) is
            when Method_Layout => To_Symbol (Item.Slot_2),
            when Label_Layout => To_Symbol (Item.Slot_1),
            when Child_Layout => To_Symbol (Item.Slot_4),
            when Value_Layout | Check_Layout | List_Layout => No_Symbol),
       Value         =>
         (if Layout_Of (Item.Head.Kind) = Value_Layout
          then Interfaces.Unsigned_64 (Item.Slot_1) + Interfaces.Unsigned_64 (Item.Slot_2) * 2 ** 32
          else 0),
       Operator      => Item.Head.Operator,
       Attribute     => Item.Head.Attribute,
       Is_Vararg     => Item.Head.Is_Vararg,
       Is_Method     => Item.Head.Is_Method,
       Is_Name_Key   => Item.Head.Is_Name_Key,
       Is_Incomplete => Item.Head.Is_Incomplete,
       Is_Last_Label => Item.Head.Is_Last_Label,
       Check_Point   =>
         (Ordinal =>
            (if Layout_Of (Item.Head.Kind) in Check_Layout | Label_Layout
             then To_Ordinal (Item.Slot_3) else 0),
          During  => Item.Head.During),
       Check_Line    =>
         (if Layout_Of (Item.Head.Kind) in Check_Layout | Label_Layout
          then To_Line (Item.Slot_4) else 1));
   pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Decode);

   --  [proof] The node Item stands for, with the spill table Spill.
   function Resolve (Item : Stored_Node; Spill : Node_Arrays.Models.Sequence) return Node
   is (if Item.Head.Spilled
          and then Item.Slot_1 in 1 .. Slot_Value (Node_Arrays.Models.Last (Spill))
       then Node_Arrays.Models.Get (Spill, Node_Position (Item.Slot_1))
       else Decode (Item))
   with Ghost;
   pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Resolve);

   --  [proof] The node at Index of the stored nodes Nodes, with the spill table Spill.
   function Model_Get
     (Nodes : Stored_Arrays.Models.Sequence;
      Spill : Node_Arrays.Models.Sequence;
      Index : Node_Position) return Node
   is (if Index <= Stored_Arrays.Models.Last (Nodes)
       then Resolve (Stored_Arrays.Models.Get (Nodes, Index), Spill)
       else (others => <>))
   with Ghost;
   pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Model_Get);

   --  [proof] Every spilled node indexes a node of the spill table.
   function Spills_Valid
     (Nodes : Stored_Arrays.Models.Sequence; Spill : Node_Arrays.Models.Sequence) return Boolean
   is (for all Index in 1 .. Stored_Arrays.Models.Last (Nodes) =>
         (if Stored_Arrays.Models.Get (Nodes, Index).Head.Spilled
          then Stored_Arrays.Models.Get (Nodes, Index).Slot_1
                 in 1 .. Slot_Value (Node_Arrays.Models.Last (Spill))))
   with Ghost;
   pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Spills_Valid);

   --  [proof] Node Item at Index is well formed against the list arena Lists.
   function Is_Well_Formed_Node
     (Item : Node; Index : Node_Position; Lists : Index_Arrays.Models.Sequence) return Boolean
   is ((for all Slot in Child_Slot => Child_Of (Item, Slot) < Index)
       and then (Item.List_Length = 0
                 or else (Item.List_First >= 1
                          and then Item.List_First <= Index_Arrays.Models.Last (Lists)
                          and then Item.List_Length
                                   <= Index_Arrays.Models.Last (Lists) - Item.List_First + 1
                          and then (for all Position in Item.List_First
                                                        .. Item.List_First + Item.List_Length - 1
                                    => Index_Arrays.Models.Get (Lists, Position)
                                         in 1 .. Index - 1))))
   with Ghost;

   function Is_Well_Formed (Tree : Syntax_Tree) return Boolean
   is ((Stored_Arrays.Length (Tree.Nodes) = 0
        or else Spills_Valid (Stored_Arrays.Model (Tree.Nodes), Node_Arrays.Model (Tree.Spill)))
       and then (for all Index in 1 .. Stored_Arrays.Length (Tree.Nodes) =>
                   Is_Well_Formed_Node
                     (Model_Get
                        (Stored_Arrays.Model (Tree.Nodes), Node_Arrays.Model (Tree.Spill), Index),
                      Index,
                      Index_Arrays.Model (Tree.Lists)))
       and then (for all Position in 1 .. Index_Arrays.Length (Tree.Waiting) =>
                   Index_Arrays.Element (Tree.Waiting, Position)
                     in 1 .. Stored_Arrays.Length (Tree.Nodes)));

   --  [proof] Growing the list arena (keeping what it held) keeps every node well formed,
   --  since a node's list lies in the part that was already there.
   procedure Lemma_Lists_Grew
     (Tree : Syntax_Tree; Old_Lists : Index_Arrays.Models.Sequence)
   with
     Ghost,
     Global => null,
     Pre    =>
       Old_Lists <= Index_Arrays.Model (Tree.Lists)
       and then (for all Index in 1 .. Stored_Arrays.Length (Tree.Nodes) =>
                   Is_Well_Formed_Node
                     (Model_Get
                        (Stored_Arrays.Model (Tree.Nodes), Node_Arrays.Model (Tree.Spill), Index),
                      Index,
                      Old_Lists)),
     Post   =>
       (for all Index in 1 .. Stored_Arrays.Length (Tree.Nodes) =>
          Is_Well_Formed_Node
            (Model_Get (Stored_Arrays.Model (Tree.Nodes), Node_Arrays.Model (Tree.Spill), Index),
             Index,
             Index_Arrays.Model (Tree.Lists)));

   procedure Lemma_Lists_Grew
     (Tree : Syntax_Tree; Old_Lists : Index_Arrays.Models.Sequence) is null;

   --  The node at Index, read from its stored form or the spill table.
   function Stored_Get (Tree : Syntax_Tree; Index : Node_Index) return Node
   with
     Global => null,
     Pre    => Index in 1 .. Node_Count (Tree),
     Post   =>
       Stored_Get'Result
       = Model_Get (Stored_Arrays.Model (Tree.Nodes), Node_Arrays.Model (Tree.Spill), Index)
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Decode);
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Resolve);
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Model_Get);
      Item : constant Stored_Node := Stored_Arrays.Element (Tree.Nodes, Index);
   begin
      if Item.Head.Spilled
        and then Item.Slot_1 in 1 .. Slot_Value (Node_Arrays.Length (Tree.Spill))
      then
         return Node_Arrays.Element (Tree.Spill, Node_Position (Item.Slot_1));
      end if;
      return Decode (Item);
   end Stored_Get;

   function Get (Tree : Syntax_Tree; Index : Node_Index) return Node
   is (Stored_Get (Tree, Index));

   function Child (Tree : Syntax_Tree; Index : Node_Index; Slot : Child_Slot) return Node_Index
   is (Child_Of (Get (Tree, Index), Slot));

   function List_Item
     (Tree : Syntax_Tree; Index : Node_Index; Position : List_Index) return Node_Index
   is
      Item : constant Node := Get (Tree, Index);
   begin
      return Index_Arrays.Element (Tree.Lists, Item.List_First + Position - 1);
   end List_Item;

   --  Adds Item (its list fields included) after the stored nodes, spilled when its stored form
   --  does not read back the same. Success is False (Nodes keeps its length) when Budget
   --  cannot pay.
   procedure Store
     (Nodes   : in out Stored_Arrays.Growable_Array;
      Spill   : in out Node_Arrays.Growable_Array;
      Budget  : in out Memory_Budget;
      Item    : Node;
      Success : out Boolean)
   with
     Global => null,
     Pre    =>
       Stored_Arrays.Length (Nodes) = 0
       or else Spills_Valid (Stored_Arrays.Model (Nodes), Node_Arrays.Model (Spill)),
     Post   =>
       Spills_Valid (Stored_Arrays.Model (Nodes), Node_Arrays.Model (Spill))
       and then Limit (Budget) = Limit (Budget)'Old
       and then (for all Index in 1 .. Stored_Arrays.Length (Nodes)'Old =>
                   Model_Get (Stored_Arrays.Model (Nodes), Node_Arrays.Model (Spill), Index)
                   = Model_Get
                       (Stored_Arrays.Model (Nodes)'Old, Node_Arrays.Model (Spill)'Old, Index))
       and then (if Success
                 then Stored_Arrays.Length (Nodes) = Stored_Arrays.Length (Nodes)'Old + 1
                      and then Model_Get
                                 (Stored_Arrays.Model (Nodes),
                                  Node_Arrays.Model (Spill),
                                  Stored_Arrays.Length (Nodes))
                               = Item
                 else Stored_Arrays.Length (Nodes) = Stored_Arrays.Length (Nodes)'Old)
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Decode);
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Resolve);
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Model_Get);
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Spills_Valid);
      Encoded : Stored_Node := Encode (Item);
   begin
      if Decode (Encoded) /= Item then
         Node_Arrays.Append (Spill, Item, Budget, Success);
         if not Success then
            return;
         end if;
         Encoded.Head.Spilled := True;
         Encoded.Slot_1 := Slot_Value (Node_Arrays.Length (Spill));
      end if;
      Stored_Arrays.Append (Nodes, Encoded, Budget, Success);
   end Store;

   --  Adds Item, well formed as the next node, as a new node: Result, or No_Node (and the tree
   --  is unchanged) when Budget cannot pay.
   procedure Add_Well_Formed
     (Tree   : in out Syntax_Tree;
      Budget : in out Memory_Budget;
      Item   : Node;
      Result : out Node_Index)
   with
     Global => null,
     Pre    =>
       Is_Well_Formed (Tree)
       and then Node_Count (Tree) < Node_Position'Last
       and then Is_Well_Formed_Node (Item, Node_Count (Tree) + 1, Index_Arrays.Model (Tree.Lists)),
     Post   =>
       Is_Well_Formed (Tree)
       and then Pending (Tree) = Pending (Tree)'Old
       and then Limit (Budget) = Limit (Budget)'Old
       and then (if Result = No_Node then Node_Count (Tree) = Node_Count (Tree)'Old
                 else Node_Count (Tree) = Node_Count (Tree)'Old + 1
                      and then Result = Node_Count (Tree))
   is
      Old_Count : constant Node_Index := Node_Count (Tree);
      Old_Nodes : constant Stored_Arrays.Models.Sequence := Stored_Arrays.Model (Tree.Nodes)
      with Ghost;
      Old_Spill : constant Node_Arrays.Models.Sequence := Node_Arrays.Model (Tree.Spill)
      with Ghost;
      Success   : Boolean;
   begin
      Store (Tree.Nodes, Tree.Spill, Budget, Item, Success);
      pragma Assert
        (for all Index in 1 .. Old_Count =>
           Model_Get (Stored_Arrays.Model (Tree.Nodes), Node_Arrays.Model (Tree.Spill), Index)
           = Model_Get (Old_Nodes, Old_Spill, Index));
      Result := (if Success then Node_Count (Tree) else No_Node);
   end Add_Well_Formed;

   procedure Add_Node
     (Tree   : in out Syntax_Tree;
      Budget : in out Memory_Budget;
      Item   : Node;
      Result : out Node_Index)
   is
      New_Item : Node := Item;
   begin
      New_Item.List_First := 0;
      New_Item.List_Length := 0;
      if Node_Count (Tree) = Node_Position'Last then
         Result := No_Node;
         return;
      end if;
      Add_Well_Formed (Tree, Budget, New_Item, Result);
   end Add_Node;

   procedure Push
     (Tree    : in out Syntax_Tree;
      Budget  : in out Memory_Budget;
      Item    : Node_Index;
      Success : out Boolean) is
   begin
      Index_Arrays.Append (Tree.Waiting, Item, Budget, Success);
   end Push;

   procedure Add_List_Node
     (Tree   : in out Syntax_Tree;
      Budget : in out Memory_Budget;
      Item   : Node;
      Mark   : List_Index;
      Result : out Node_Index)
   is
      Top        : constant List_Index := Pending (Tree);
      Old_Length : constant List_Index := Index_Arrays.Length (Tree.Lists);
      Old_Lists  : constant Index_Arrays.Models.Sequence := Index_Arrays.Model (Tree.Lists)
      with Ghost;
      New_Item   : Node := Item;
      Success    : Boolean;
   begin
      Result := No_Node;
      pragma Assert
        (for all Index in 1 .. Stored_Arrays.Length (Tree.Nodes) =>
           Is_Well_Formed_Node
             (Model_Get (Stored_Arrays.Model (Tree.Nodes), Node_Arrays.Model (Tree.Spill), Index),
              Index,
              Old_Lists));
      for Position in Mark + 1 .. Top loop
         Index_Arrays.Append
           (Tree.Lists, Index_Arrays.Element (Tree.Waiting, Position), Budget, Success);
         if not Success then
            Lemma_Lists_Grew (Tree, Old_Lists);
            Index_Arrays.Truncate (Tree.Waiting, Mark);
            return;
         end if;
         pragma Loop_Invariant (Index_Arrays.Length (Tree.Lists) = Old_Length + (Position - Mark));
         pragma Loop_Invariant (Old_Lists <= Index_Arrays.Model (Tree.Lists));
         pragma Loop_Invariant
           (for all Added in Old_Length + 1 .. Index_Arrays.Length (Tree.Lists) =>
              Index_Arrays.Element (Tree.Lists, Added)
                = Index_Arrays.Element (Tree.Waiting, Mark + (Added - Old_Length)));
         pragma Loop_Invariant (Limit (Budget) = Limit (Budget)'Loop_Entry);
         pragma Loop_Invariant
           (for all Index in 1 .. Stored_Arrays.Length (Tree.Nodes) =>
              Is_Well_Formed_Node
                (Model_Get
                   (Stored_Arrays.Model (Tree.Nodes), Node_Arrays.Model (Tree.Spill), Index),
                 Index,
                 Old_Lists));
      end loop;
      Lemma_Lists_Grew (Tree, Old_Lists);
      New_Item.List_Length := Top - Mark;
      New_Item.List_First := (if Top > Mark then Old_Length + 1 else 0);
      pragma Assert
        (for all Added in Old_Length + 1 .. Index_Arrays.Length (Tree.Lists) =>
           Index_Arrays.Element (Tree.Lists, Added) in 1 .. Node_Count (Tree));
      if Node_Count (Tree) < Node_Position'Last then
         pragma Assert
           (Is_Well_Formed_Node
              (New_Item, Node_Count (Tree) + 1, Index_Arrays.Model (Tree.Lists)));
         Add_Well_Formed (Tree, Budget, New_Item, Result);
      end if;
      Index_Arrays.Truncate (Tree.Waiting, Mark);
   end Add_List_Node;

   procedure Drop_Pending (Tree : in out Syntax_Tree; Mark : List_Index) is
   begin
      Index_Arrays.Truncate (Tree.Waiting, Mark);
   end Drop_Pending;

   procedure Swap (Left, Right : in out Syntax_Tree) is
   begin
      Stored_Arrays.Swap (Left.Nodes, Right.Nodes);
      Node_Arrays.Swap (Left.Spill, Right.Spill);
      Index_Arrays.Swap (Left.Lists, Right.Lists);
      Index_Arrays.Swap (Left.Waiting, Right.Waiting);
   end Swap;

   procedure Clear (Tree : in out Syntax_Tree; Budget : in out Memory_Budget) is
   begin
      Stored_Arrays.Clear (Tree.Nodes, Budget);
      Node_Arrays.Clear (Tree.Spill, Budget);
      Index_Arrays.Clear (Tree.Lists, Budget);
      Index_Arrays.Clear (Tree.Waiting, Budget);
   end Clear;

end Pyro.Syntax_Trees;
