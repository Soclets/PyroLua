--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  The syntax tree arena: nodes indexed by Node_Index, children always older than their parent.

with Interfaces;
with Pyro.Diagnostics;    use Pyro.Diagnostics;
with Pyro.Growable_Arrays;
with Pyro.Memory_Budgets; use Pyro.Memory_Budgets;
with Pyro.Sources;        use Pyro.Sources;
with Pyro.Symbols;        use Pyro.Symbols;

package Pyro.Syntax_Trees with SPARK_Mode => On, Always_Terminates is

   --  The most nodes a tree holds.
   Maximum_Nodes : constant := 2 ** 27;

   --  A node of a tree, or No_Node.
   type Node_Index is range 0 .. Maximum_Nodes;
   No_Node : constant Node_Index := 0;

   --  A position in the arena of child lists, or in the stack lists are built on.
   type List_Index is range 0 .. Maximum_Nodes;

   type Child_Slot is range 1 .. 3;

   --  What a node is. The comments give the children (1, 2, 3), the list, and the payload.
   type Node_Kind is
     (
      --  Expressions.
      Nil_Literal, True_Literal, False_Literal,
      Vararg_Expression,
      Integer_Literal,       --  Value: the integer's bits
      Float_Literal,         --  Value: the float's bits
      String_Literal,        --  Symbol: the bytes
      Function_Expression,   --  1 Function_Body
      Table_Constructor,     --  list: fields (expressions or Named_Field)
      Named_Field,           --  1 key, 2 value; Is_Name_Key for "name = value"
      Binary_Operation,      --  1 left, 2 right; Operator
      Unary_Operation,       --  1 operand; Operator
      Name_Expression,       --  Symbol: the name
      Index_Expression,      --  1 object, 2 key; Is_Name_Key for "object.name"
      Call_Expression,       --  1 function; list: arguments
      Method_Call,           --  1 object; Symbol: method name; list: arguments
      Parenthesized,         --  1 expression
      --  Statements.
      Local_Statement,       --  1 Name_List, 2 Expression_List (or none)
      Local_Function,        --  1 Local_Name, 2 Function_Body
      Assignment,            --  1 Expression_List of Assignment_Target, 2 Expression_List
      Assignment_Target,     --  1 the variable; Check: when PUC checks it is not constant
      Call_Statement,        --  1 call
      Do_Statement,          --  1 Block
      While_Statement,       --  1 condition, 2 Block
      Repeat_Statement,      --  1 Block, 2 condition (sees the block's locals)
      If_Statement,          --  1 else Block (or none); list: If_Clause
      If_Clause,             --  1 condition, 2 Block
      Numeric_For,           --  1 Local_Name, 2 Expression_List (start, limit, step), 3 Block
      Generic_For,           --  1 Name_List, 2 Expression_List, 3 Block
      Function_Statement,    --  1 name expression, 2 Function_Body; Check: constant check
      Return_Statement,      --  1 Expression_List (or none)
      Break_Statement,
      Goto_Statement,        --  Symbol: the label
      --  Symbol: the label; list: the labels right after it, which PUC Lua declares first;
      --  Check: the duplicate and scope checks.
      Label_Statement,
      --  Structure.
      Block,                 --  list: statements
      Expression_List,       --  list: expressions
      Name_List,             --  list: Local_Name
      Local_Name,            --  Symbol: the name; Attribute
      --  1 Name_List (parameters), 2 Block; Is_Vararg, Is_Method; Check: when PUC Lua closes
      --  the function.
      Function_Body,
      Missing);              --  a part that a syntax error left out

   --  Operators of Binary_Operation and Unary_Operation.
   type Operator_Kind is
     (No_Operator,
      Add, Subtract, Multiply, Divide, Floor_Divide, Modulo, Power, Concatenate,
      Equal, Not_Equal, Less, Less_Equal, Greater, Greater_Equal, And_Then, Or_Else,
      Bitwise_And, Bitwise_Or, Bitwise_Exclusive_Or, Shift_Left, Shift_Right,
      Negate, Logical_Not, Length, Bitwise_Not);

   --  [lua §3.3.7] The attribute of a local variable.
   type Attribute_Kind is (Regular, Constant_Attribute, Close_Attribute);

   --  One node. The list of a node is given by its List_First and List_Length.
   type Node is record
      Kind        : Node_Kind := Missing;
      --  The node's bytes in the source, and the line PUC Lua gives the construct.
      First       : Source_Position := 1;
      Last        : Span_End := 0;
      Line        : Line_Number := 1;
      --  Children 1, 2 and 3 (separate components, so node equality is logical equality).
      First_Child  : Node_Index := No_Node;
      Second_Child : Node_Index := No_Node;
      Third_Child  : Node_Index := No_Node;
      List_First  : List_Index := 0;
      List_Length : List_Index := 0;
      Symbol      : Symbol_Index := No_Symbol;
      Value       : Interfaces.Unsigned_64 := 0;
      Operator    : Operator_Kind := No_Operator;
      Attribute   : Attribute_Kind := Regular;
      Is_Vararg   : Boolean := False;
      Is_Method   : Boolean := False;
      Is_Name_Key : Boolean := False;
      --  A syntax error cut this block or function short.
      Is_Incomplete : Boolean := False;
      --  A label that is the last statement of its block (not counting "until").
      Is_Last_Label : Boolean := False;
      --  When PUC Lua makes this node's semantic check, and its line then.
      Check_Point : Detection_Point := (Ordinal => 0, During => Parsing);
      Check_Line  : Line_Number := 1;
   end record;

   --  Child Slot of Item.
   function Child_Of (Item : Node; Slot : Child_Slot) return Node_Index
   is (case Slot is
         when 1 => Item.First_Child,
         when 2 => Item.Second_Child,
         when 3 => Item.Third_Child);

   --  A syntax tree, with a stack on which lists are built before their node exists. It owns
   --  heap memory: release it with Clear.
   type Syntax_Tree is limited private
   with
     Default_Initial_Condition =>
       Is_Well_Formed (Syntax_Tree)
       and then Node_Count (Syntax_Tree) = 0
       and then Pending (Syntax_Tree) = 0
       and then Is_Released (Syntax_Tree);

   --  The number of nodes.
   function Node_Count (Tree : Syntax_Tree) return Node_Index
   with Global => null;

   --  The number of list items waiting on the stack.
   function Pending (Tree : Syntax_Tree) return List_Index
   with Global => null;

   --  [proof] Every child and list item of a node is an older node (a smaller index), every
   --  list lies inside the list arena, and every waiting list item is a node. This makes the
   --  tree acyclic and every walk well-founded.
   function Is_Well_Formed (Tree : Syntax_Tree) return Boolean
   with Ghost, Global => null;

   --  The node at Index.
   function Get (Tree : Syntax_Tree; Index : Node_Index) return Node
   with Global => null, Pre => Index in 1 .. Node_Count (Tree);

   --  Child Slot of node Index: No_Node or an older node.
   function Child (Tree : Syntax_Tree; Index : Node_Index; Slot : Child_Slot) return Node_Index
   with
     Global => null,
     Pre    => Is_Well_Formed (Tree) and then Index in 1 .. Node_Count (Tree),
     Post   => Child'Result < Index and then Child'Result = Child_Of (Get (Tree, Index), Slot);

   --  Item Position of the list of node Index: an older node.
   function List_Item
     (Tree : Syntax_Tree; Index : Node_Index; Position : List_Index) return Node_Index
   with
     Global => null,
     Pre    =>
       Is_Well_Formed (Tree)
       and then Index in 1 .. Node_Count (Tree)
       and then Position in 1 .. Get (Tree, Index).List_Length,
     Post   => List_Item'Result in 1 .. Index - 1;

   --  Adds Item as a new node, with no list. Its children must be nodes of the tree already.
   --  Result is the new node, or No_Node (and the tree is unchanged) when Budget cannot pay.
   procedure Add_Node
     (Tree   : in out Syntax_Tree;
      Budget : in out Memory_Budget;
      Item   : Node;
      Result : out Node_Index)
   with
     Global => null,
     Pre    =>
       Is_Well_Formed (Tree)
       and then (for all Slot in Child_Slot => Child_Of (Item, Slot) <= Node_Count (Tree)),
     Post   =>
       Is_Well_Formed (Tree)
       and then Pending (Tree) = Pending (Tree)'Old
       and then Limit (Budget) = Limit (Budget)'Old
       and then (if Result = No_Node then Node_Count (Tree) = Node_Count (Tree)'Old
                 else Node_Count (Tree) = Node_Count (Tree)'Old + 1
                      and then Result = Node_Count (Tree));

   --  Puts Item on the stack of waiting list items.
   procedure Push
     (Tree    : in out Syntax_Tree;
      Budget  : in out Memory_Budget;
      Item    : Node_Index;
      Success : out Boolean)
   with
     Global => null,
     Pre    => Is_Well_Formed (Tree) and then Item in 1 .. Node_Count (Tree),
     Post   =>
       Is_Well_Formed (Tree)
       and then Node_Count (Tree) = Node_Count (Tree)'Old
       and then Limit (Budget) = Limit (Budget)'Old
       and then (if Success then Pending (Tree) = Pending (Tree)'Old + 1
                 else Pending (Tree) = Pending (Tree)'Old);

   --  Adds Item as a new node whose list is the items waiting above Mark, which leave the stack.
   --  Its children must be nodes of the tree already. Result is No_Node (the tree keeps its
   --  nodes) when Budget cannot pay.
   procedure Add_List_Node
     (Tree   : in out Syntax_Tree;
      Budget : in out Memory_Budget;
      Item   : Node;
      Mark   : List_Index;
      Result : out Node_Index)
   with
     Global => null,
     Pre    =>
       Is_Well_Formed (Tree)
       and then Mark <= Pending (Tree)
       and then (for all Slot in Child_Slot => Child_Of (Item, Slot) <= Node_Count (Tree)),
     Post   =>
       Is_Well_Formed (Tree)
       and then Pending (Tree) = Mark
       and then Limit (Budget) = Limit (Budget)'Old
       and then (if Result = No_Node then Node_Count (Tree) = Node_Count (Tree)'Old
                 else Node_Count (Tree) = Node_Count (Tree)'Old + 1
                      and then Result = Node_Count (Tree));

   --  Drops the items waiting above Mark.
   procedure Drop_Pending (Tree : in out Syntax_Tree; Mark : List_Index)
   with
     Global => null,
     Pre    => Is_Well_Formed (Tree) and then Mark <= Pending (Tree),
     Post   =>
       Is_Well_Formed (Tree)
       and then Pending (Tree) = Mark
       and then Node_Count (Tree) = Node_Count (Tree)'Old;

   --  Exchanges the nodes (and memory) of Left and Right.
   procedure Swap (Left, Right : in out Syntax_Tree)
   with
     Global => null,
     Pre    => Is_Well_Formed (Left) and then Is_Well_Formed (Right),
     Post   =>
       Is_Well_Formed (Left)
       and then Is_Well_Formed (Right)
       and then Node_Count (Left) = Node_Count (Right)'Old
       and then Node_Count (Right) = Node_Count (Left)'Old
       and then Pending (Left) = Pending (Right)'Old
       and then Pending (Right) = Pending (Left)'Old
       and then Is_Released (Left) = Is_Released (Right)'Old
       and then Is_Released (Right) = Is_Released (Left)'Old;

   --  Removes every node and releases the memory.
   procedure Clear (Tree : in out Syntax_Tree; Budget : in out Memory_Budget)
   with
     Global => null,
     Post   =>
       Is_Well_Formed (Tree)
       and then Node_Count (Tree) = 0
       and then Pending (Tree) = 0
       and then Is_Released (Tree)
       and then Limit (Budget) = Limit (Budget)'Old;

   --  True when the tree holds no heap memory.
   function Is_Released (Tree : Syntax_Tree) return Boolean
   with Global => null;

private

   subtype Node_Position is Node_Index range 1 .. Node_Index'Last;
   subtype List_Position is List_Index range 1 .. List_Index'Last;

   package Node_Arrays is new Pyro.Growable_Arrays
     (Index => Node_Position, Element_Type => Node, Default_Element => (others => <>),
      Element_Bytes => 96);

   package Index_Arrays is new Pyro.Growable_Arrays
     (Index => List_Position, Element_Type => Node_Index, Default_Element => No_Node,
      Element_Bytes => 4);

   type Syntax_Tree is limited record
      Nodes   : Node_Arrays.Growable_Array;
      Lists   : Index_Arrays.Growable_Array;
      Waiting : Index_Arrays.Growable_Array;
   end record;

   function Node_Count (Tree : Syntax_Tree) return Node_Index
   is (Node_Arrays.Length (Tree.Nodes));

   function Pending (Tree : Syntax_Tree) return List_Index
   is (Index_Arrays.Length (Tree.Waiting));

   function Get (Tree : Syntax_Tree; Index : Node_Index) return Node
   is (Node_Arrays.Element (Tree.Nodes, Index));

   use type Index_Arrays.Models.Sequence;

   function Is_Released (Tree : Syntax_Tree) return Boolean
   is (Node_Arrays.Is_Released (Tree.Nodes)
       and then Index_Arrays.Is_Released (Tree.Lists)
       and then Index_Arrays.Is_Released (Tree.Waiting));

end Pyro.Syntax_Trees;
