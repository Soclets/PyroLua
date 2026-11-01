--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  Scope analysis: binds every name to its declaration and reports the errors PUC Lua finds
--  through scopes (const assignment, goto and labels, break).

with Pyro.Diagnostic_Lists;
with Pyro.Growable_Arrays;
with Pyro.Memory_Budgets; use Pyro.Memory_Budgets;
with Pyro.Sources;        use Pyro.Sources;
with Pyro.Symbols;        use Pyro.Symbols;
with Pyro.Syntax_Trees;   use Pyro.Syntax_Trees;

package Pyro.Resolver with SPARK_Mode => On, Always_Terminates is

   --  What a name refers to.
   type Binding_Kind is
     (Unbound,         --  not a name use (or not reached)
      Local_Variable,  --  a local of the same function
      Upvalue,         --  a local of an enclosing function
      Global);         --  a field of _ENV

   --  The binding of one name: its kind and, for locals and upvalues, the Local_Name node that
   --  declares it (No_Node for the implicit "self" of a method).
   type Binding is record
      Kind        : Binding_Kind := Unbound;
      Declaration : Node_Index := No_Node;
   end record;

   --  The bindings of a tree's Name_Expression nodes, by node. It owns heap memory: release it
   --  with Clear.
   type Binding_Table is limited private;

   --  The binding of node Index (Unbound for nodes that are not names).
   function Binding_Of (Table : Binding_Table; Index : Node_Index) return Binding
   with Global => null;

   --  [puc lparser.c] Walks the tree from Root (the main Function_Body) as PUC's parser walks
   --  the source, binding names and appending to Problems every error PUC would raise through
   --  scopes. Each error records PUC's line and detection point (the nodes' checks). In a
   --  function cut short by a syntax error, gotos left without a label are not reported, since
   --  their label could be in the part that is missing.
   procedure Resolve
     (Tree     : Syntax_Tree;
      Root     : Node_Index;
      Symbols  : Symbol_Table;
      Budget   : in out Memory_Budget;
      Problems : in out Diagnostic_Lists.Growable_Array;
      Bindings : in out Binding_Table)
   with
     Global => null,
     Pre    => Is_Well_Formed (Tree) and then Root <= Node_Count (Tree) and then Is_Valid (Symbols),
     Post   => Limit (Budget) = Limit (Budget)'Old;

   --  Releases the table's memory.
   procedure Clear (Table : in out Binding_Table; Budget : in out Memory_Budget)
   with
     Global => null,
     Post   => Is_Released (Table) and then Limit (Budget) = Limit (Budget)'Old;

   --  True when the table holds no heap memory.
   function Is_Released (Table : Binding_Table) return Boolean
   with Global => null;

private

   Maximum_Entries : constant := 2 ** 27;
   type Entry_Index is range 0 .. Maximum_Entries;
   subtype Entry_Position is Entry_Index range 1 .. Entry_Index'Last;

   --  An active local variable. Hidden variables (the "(for state)" of loops) have no name.
   type Variable_Entry is record
      Name        : Symbol_Index := No_Symbol;
      Attribute   : Attribute_Kind := Regular;
      Declaration : Node_Index := No_Node;
      Owner       : Entry_Index := 0;
   end record;

   --  An open function: where its variables, labels, gotos and blocks start.
   type Function_Entry is record
      First_Variable : Entry_Index := 0;
      First_Label    : Entry_Index := 0;
      First_Goto     : Entry_Index := 0;
      Block_Base     : Entry_Index := 0;
      Body_Node      : Node_Index := No_Node;
   end record;

   --  [puc lparser.c:BlockCnt] An open block. Active counts the variables active on entry.
   type Block_Entry is record
      Active      : Entry_Index := 0;
      First_Label : Entry_Index := 0;
      First_Goto  : Entry_Index := 0;
      Is_Loop     : Boolean := False;
   end record;

   --  [puc lparser.c:Labeldesc] A visible label or a pending goto ("break" for a break).
   type Jump_Entry is record
      Name     : Symbol_Index := No_Symbol;
      Is_Break : Boolean := False;
      Line     : Line_Number := 1;
      Active   : Entry_Index := 0;
      Node     : Node_Index := No_Node;
   end record;

   --  A node being walked, and how far its walk has gone.
   type Frame is record
      Node   : Node_Index := No_Node;
      Step   : Natural := 0;
      Scoped : Boolean := True;
   end record;

   subtype Node_Position is Node_Index range 1 .. Node_Index'Last;

   package Binding_Arrays is new Pyro.Growable_Arrays
     (Index => Node_Position, Element_Type => Binding, Default_Element => (others => <>),
      Element_Bytes => 8);

   type Binding_Table is limited record
      Items : Binding_Arrays.Growable_Array;
   end record;

   function Binding_Of (Table : Binding_Table; Index : Node_Index) return Binding
   is (if Index in 1 .. Binding_Arrays.Length (Table.Items)
       then Binding_Arrays.Element (Table.Items, Index)
       else (Kind => Unbound, Declaration => No_Node));

   function Is_Released (Table : Binding_Table) return Boolean
   is (Binding_Arrays.Is_Released (Table.Items));

end Pyro.Resolver;
