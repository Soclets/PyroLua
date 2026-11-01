--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  The syntax tree arena: nodes indexed by Node_Index, children always older than their parent.

package body Pyro.Syntax_Trees with SPARK_Mode => On is

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
   is ((for all Index in 1 .. Node_Arrays.Length (Tree.Nodes) =>
          Is_Well_Formed_Node
            (Node_Arrays.Element (Tree.Nodes, Index), Index, Index_Arrays.Model (Tree.Lists)))
       and then (for all Position in 1 .. Index_Arrays.Length (Tree.Waiting) =>
                   Index_Arrays.Element (Tree.Waiting, Position)
                     in 1 .. Node_Arrays.Length (Tree.Nodes)));

   --  [proof] Growing the list arena (keeping what it held) keeps every node well formed,
   --  since a node's list lies in the part that was already there.
   procedure Lemma_Lists_Grew
     (Tree : Syntax_Tree; Old_Lists : Index_Arrays.Models.Sequence)
   with
     Ghost,
     Global => null,
     Pre    =>
       Old_Lists <= Index_Arrays.Model (Tree.Lists)
       and then (for all Index in 1 .. Node_Arrays.Length (Tree.Nodes) =>
                   Is_Well_Formed_Node (Node_Arrays.Element (Tree.Nodes, Index), Index, Old_Lists)),
     Post   =>
       (for all Index in 1 .. Node_Arrays.Length (Tree.Nodes) =>
          Is_Well_Formed_Node
            (Node_Arrays.Element (Tree.Nodes, Index), Index, Index_Arrays.Model (Tree.Lists)));

   procedure Lemma_Lists_Grew
     (Tree : Syntax_Tree; Old_Lists : Index_Arrays.Models.Sequence) is null;

   function Child (Tree : Syntax_Tree; Index : Node_Index; Slot : Child_Slot) return Node_Index
   is (Child_Of (Get (Tree, Index), Slot));

   function List_Item
     (Tree : Syntax_Tree; Index : Node_Index; Position : List_Index) return Node_Index
   is
      Item : constant Node := Get (Tree, Index);
   begin
      return Index_Arrays.Element (Tree.Lists, Item.List_First + Position - 1);
   end List_Item;

   procedure Add_Node
     (Tree   : in out Syntax_Tree;
      Budget : in out Memory_Budget;
      Item   : Node;
      Result : out Node_Index)
   is
      New_Item : Node := Item;
      Success  : Boolean;
   begin
      New_Item.List_First := 0;
      New_Item.List_Length := 0;
      Node_Arrays.Append (Tree.Nodes, New_Item, Budget, Success);
      Result := (if Success then Node_Count (Tree) else No_Node);
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
      end loop;
      Lemma_Lists_Grew (Tree, Old_Lists);
      New_Item.List_Length := Top - Mark;
      New_Item.List_First := (if Top > Mark then Old_Length + 1 else 0);
      pragma Assert
        (for all Added in Old_Length + 1 .. Index_Arrays.Length (Tree.Lists) =>
           Index_Arrays.Element (Tree.Lists, Added) in 1 .. Node_Count (Tree));
      Node_Arrays.Append (Tree.Nodes, New_Item, Budget, Success);
      if Success then
         Result := Node_Count (Tree);
      end if;
      Index_Arrays.Truncate (Tree.Waiting, Mark);
   end Add_List_Node;

   procedure Drop_Pending (Tree : in out Syntax_Tree; Mark : List_Index) is
   begin
      Index_Arrays.Truncate (Tree.Waiting, Mark);
   end Drop_Pending;

   procedure Swap (Left, Right : in out Syntax_Tree) is
   begin
      Node_Arrays.Swap (Left.Nodes, Right.Nodes);
      Index_Arrays.Swap (Left.Lists, Right.Lists);
      Index_Arrays.Swap (Left.Waiting, Right.Waiting);
   end Swap;

   procedure Clear (Tree : in out Syntax_Tree; Budget : in out Memory_Budget) is
   begin
      Node_Arrays.Clear (Tree.Nodes, Budget);
      Index_Arrays.Clear (Tree.Lists, Budget);
      Index_Arrays.Clear (Tree.Waiting, Budget);
   end Clear;

end Pyro.Syntax_Trees;
