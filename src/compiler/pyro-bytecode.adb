--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  Lua 5.4's instruction set as typed records, compiled prototypes, and their validity.

package body Pyro.Bytecode with SPARK_Mode => On is

   --  The entry of prototype P.
   function Entry_Of (Item : Chunk; P : Prototype_Index) return Prototype_Entry
   is (Prototype_Arrays.Element (Item.Prototypes, P))
   with Pre => P in 1 .. Prototype_Count (Item);

   --  The arena position of entry Number of a prototype whose entries start after Base.
   function Position (Base : Entry_Count; Number : Entry_Number) return Arena_Position
   is (Arena_Position (Base + Number + 1))
   with Pre => Base + Number < Maximum_Entries;

   --  Every array of prototype P lies before the next prototype's entries.
   function Prototype_Well_Formed (Item : Chunk; P : Prototype_Index) return Boolean
   is (P in 1 .. Prototype_Count (Item)
       and then Prototype_Arrays.Element (Item.Prototypes, P).Code_Base
                + Prototype_Arrays.Element (Item.Prototypes, P).Code_Length <= Item.Pending_Code
       and then Prototype_Arrays.Element (Item.Prototypes, P).Constant_Base
                + Prototype_Arrays.Element (Item.Prototypes, P).Constant_Count
                <= Item.Pending_Constants
       and then Prototype_Arrays.Element (Item.Prototypes, P).Upvalue_Base
                + Prototype_Arrays.Element (Item.Prototypes, P).Upvalue_Count
                <= Item.Pending_Upvalues
       and then Prototype_Arrays.Element (Item.Prototypes, P).Local_Base
                + Prototype_Arrays.Element (Item.Prototypes, P).Local_Count
                <= Item.Pending_Locals
       and then Prototype_Arrays.Element (Item.Prototypes, P).Child_Base
                + Prototype_Arrays.Element (Item.Prototypes, P).Child_Count
                <= Item.Pending_Children);

   function Is_Well_Formed (Item : Chunk) return Boolean
   is (Line_Arrays.Length (Item.Lines) = Instruction_Arrays.Length (Item.Instructions)
       and then Item.Pending_Code <= Natural (Instruction_Arrays.Length (Item.Instructions))
       and then Item.Pending_Constants <= Natural (Constant_Arrays.Length (Item.Constants))
       and then Item.Pending_Upvalues <= Natural (Upvalue_Arrays.Length (Item.Upvalues))
       and then Item.Pending_Locals <= Natural (Local_Arrays.Length (Item.Locals))
       and then Item.Pending_Children <= Natural (Child_Arrays.Length (Item.Children))
       and then (for all P in 1 .. Prototype_Count (Item) => Prototype_Well_Formed (Item, P)));
   pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Is_Well_Formed);

   function Header (Item : Chunk; P : Prototype_Index) return Prototype_Header
   is (Entry_Of (Item, P).Facts);

   function Code_Length (Item : Chunk; P : Prototype_Index) return Entry_Count
   is (Entry_Of (Item, P).Code_Length);

   function Constant_Count (Item : Chunk; P : Prototype_Index) return Entry_Count
   is (Entry_Of (Item, P).Constant_Count);

   function Upvalue_Count (Item : Chunk; P : Prototype_Index) return Entry_Count
   is (Entry_Of (Item, P).Upvalue_Count);

   function Local_Count (Item : Chunk; P : Prototype_Index) return Entry_Count
   is (Entry_Of (Item, P).Local_Count);

   function Child_Count (Item : Chunk; P : Prototype_Index) return Entry_Count
   is (Entry_Of (Item, P).Child_Count);

   --  Instruction PC of prototype P, with no contract that mentions validity.
   function Raw_Instruction (Item : Chunk; P : Prototype_Index; PC : Entry_Number)
      return Instruction
   with
     Pre =>
       Is_Well_Formed (Item)
       and then P in 1 .. Prototype_Count (Item)
       and then PC < Code_Length (Item, P);

   function Raw_Instruction (Item : Chunk; P : Prototype_Index; PC : Entry_Number)
      return Instruction
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Is_Well_Formed);
   begin
      pragma Assert (Prototype_Well_Formed (Item, P));
      return Instruction_Arrays.Element
        (Item.Instructions, Position (Entry_Of (Item, P).Code_Base, PC));
   end Raw_Instruction;

   function Opcode_At (Item : Chunk; P : Prototype_Index; PC : Entry_Number) return Opcode
   is (Raw_Instruction (Item, P, PC).Operation);

   function Line_At
     (Item : Chunk; P : Prototype_Index; PC : Entry_Number) return Line_Number
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Is_Well_Formed);
   begin
      pragma Assert (Prototype_Well_Formed (Item, P));
      return Line_Arrays.Element (Item.Lines, Position (Entry_Of (Item, P).Code_Base, PC));
   end Line_At;

   function Constant_At
     (Item : Chunk; P : Prototype_Index; Number : Entry_Number) return Constant_Value
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Is_Well_Formed);
   begin
      pragma Assert (Prototype_Well_Formed (Item, P));
      return Constant_Arrays.Element
        (Item.Constants, Position (Entry_Of (Item, P).Constant_Base, Number));
   end Constant_At;

   function Upvalue_At
     (Item : Chunk; P : Prototype_Index; Number : Entry_Number) return Upvalue_Description
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Is_Well_Formed);
   begin
      pragma Assert (Prototype_Well_Formed (Item, P));
      return Upvalue_Arrays.Element
        (Item.Upvalues, Position (Entry_Of (Item, P).Upvalue_Base, Number));
   end Upvalue_At;

   function Local_At
     (Item : Chunk; P : Prototype_Index; Number : Entry_Number) return Local_Variable
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Is_Well_Formed);
   begin
      pragma Assert (Prototype_Well_Formed (Item, P));
      return Local_Arrays.Element (Item.Locals, Position (Entry_Of (Item, P).Local_Base, Number));
   end Local_At;

   --  Child Number of P as stored (Is_Valid checks it is an earlier prototype).
   function Raw_Child
     (Item : Chunk; P : Prototype_Index; Number : Entry_Number) return Prototype_Index
   with
     Pre =>
       Is_Well_Formed (Item)
       and then P in 1 .. Prototype_Count (Item)
       and then Number < Child_Count (Item, P);

   function Raw_Child
     (Item : Chunk; P : Prototype_Index; Number : Entry_Number) return Prototype_Index
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Is_Well_Formed);
   begin
      pragma Assert (Prototype_Well_Formed (Item, P));
      return Child_Arrays.Element
        (Item.Children, Position (Entry_Of (Item, P).Child_Base, Number));
   end Raw_Child;

   function Child_At
     (Item : Chunk; P : Prototype_Index; Number : Entry_Number) return Prototype_Index
   is (if Raw_Child (Item, P, Number) < P then Raw_Child (Item, P, Number) else No_Prototype);

   function Follows_Open_Results
     (Item : Chunk; P : Prototype_Index; PC : Entry_Number) return Boolean
   is (PC > 0
       and then (Raw_Instruction (Item, P, PC - 1).Operation = Tail_Call
                 or else (Raw_Instruction (Item, P, PC - 1).Operation in Call | Vararg
                          and then Raw_Instruction (Item, P, PC - 1).C = 0)));

   --  Every upvalue that child prototype Child captures is a register or an upvalue of P.
   function Captures_Valid (Item : Chunk; P, Child : Prototype_Index) return Boolean
   is (for all Number in 0 .. Upvalue_Count (Item, Child) - 1 =>
         (if Upvalue_At (Item, Child, Number).In_Stack
          then Is_Register (Item, P, Natural (Upvalue_At (Item, Child, Number).Index))
          else Natural (Upvalue_At (Item, Child, Number).Index) < Upvalue_Count (Item, P)))
   with
     Pre =>
       Is_Well_Formed (Item)
       and then P in 1 .. Prototype_Count (Item)
       and then Child in 1 .. Prototype_Count (Item);

   --  Every instruction of prototype P satisfies Instruction_Valid.
   function Instructions_Valid (Item : Chunk; P : Prototype_Index) return Boolean
   is (for all PC in 0 .. Code_Length (Item, P) - 1 =>
         Instruction_Valid (Item, P, PC, Raw_Instruction (Item, P, PC)))
   with Pre => Is_Well_Formed (Item) and then P in 1 .. Prototype_Count (Item);
   pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Instructions_Valid);

   --  The facts of prototype P besides its instructions (see Is_Valid).
   function Prototype_Facts_Valid (Item : Chunk; P : Prototype_Index) return Boolean
   is (Code_Length (Item, P) > 0
       and then Opcode_At (Item, P, Code_Length (Item, P) - 1)
                  in Return_Values | Return_None | Return_One | Jump
       and then Header (Item, P).Stack_Size >= 2
       and then Header (Item, P).Parameter_Count <= Header (Item, P).Stack_Size
       and then (if Header (Item, P).Is_Vararg then Opcode_At (Item, P, 0) = Vararg_Prepare))
   with Pre => Is_Well_Formed (Item) and then P in 1 .. Prototype_Count (Item);
   pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Prototype_Facts_Valid);

   --  The children of prototype P are earlier prototypes, and capture only what P has.
   function Children_Valid (Item : Chunk; P : Prototype_Index) return Boolean
   is (for all Number in 0 .. Child_Count (Item, P) - 1 =>
         Raw_Child (Item, P, Number) in 1 .. P - 1
         and then Captures_Valid (Item, P, Raw_Child (Item, P, Number)))
   with Pre => Is_Well_Formed (Item) and then P in 1 .. Prototype_Count (Item);
   pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Children_Valid);

   function Is_Valid (Item : Chunk) return Boolean
   is (Is_Well_Formed (Item)
       and then (for all P in 1 .. Prototype_Count (Item) => Instructions_Valid (Item, P))
       and then (for all P in 1 .. Prototype_Count (Item) => Prototype_Facts_Valid (Item, P))
       and then (for all P in 1 .. Prototype_Count (Item) => Children_Valid (Item, P)));
   pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Is_Valid);

   function Instruction_At
     (Item : Chunk; P : Prototype_Index; PC : Entry_Number) return Instruction
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Is_Valid);
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Instructions_Valid);
   begin
      --  Unfolds Is_Valid to the prototype, so the prover instantiates its quantifier on PC.
      pragma Assert (if Is_Valid (Item) then Instructions_Valid (Item, P));
      return Raw_Instruction (Item, P, PC);
   end Instruction_At;

   procedure Lemma_Valid_Prototype (Item : Chunk; P : Prototype_Index) is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Is_Valid);
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Prototype_Facts_Valid);
   begin
      pragma Assert (Prototype_Facts_Valid (Item, P));
   end Lemma_Valid_Prototype;

   procedure Append_Instruction
     (Item    : in out Chunk;
      Budget  : in out Memory_Budget;
      Value   : Instruction;
      Line    : Line_Number;
      Success : out Boolean)
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Is_Well_Formed);
   begin
      if Instruction_Arrays.Length (Item.Instructions) = Arena_Position'Last then
         Success := False;
         return;
      end if;
      Line_Arrays.Append (Item.Lines, Line, Budget, Success);
      if not Success then
         return;
      end if;
      Instruction_Arrays.Append (Item.Instructions, Value, Budget, Success);
      if not Success then
         Line_Arrays.Truncate (Item.Lines, Line_Arrays.Length (Item.Lines) - 1);
      end if;
   end Append_Instruction;

   procedure Append_Constant
     (Item    : in out Chunk;
      Budget  : in out Memory_Budget;
      Value   : Constant_Value;
      Success : out Boolean)
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Is_Well_Formed);
   begin
      Constant_Arrays.Append (Item.Constants, Value, Budget, Success);
   end Append_Constant;

   procedure Append_Upvalue
     (Item    : in out Chunk;
      Budget  : in out Memory_Budget;
      Value   : Upvalue_Description;
      Success : out Boolean)
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Is_Well_Formed);
   begin
      Upvalue_Arrays.Append (Item.Upvalues, Value, Budget, Success);
   end Append_Upvalue;

   procedure Append_Local
     (Item    : in out Chunk;
      Budget  : in out Memory_Budget;
      Value   : Local_Variable;
      Success : out Boolean)
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Is_Well_Formed);
   begin
      Local_Arrays.Append (Item.Locals, Value, Budget, Success);
   end Append_Local;

   procedure Append_Child
     (Item    : in out Chunk;
      Budget  : in out Memory_Budget;
      Child   : Prototype_Index;
      Success : out Boolean)
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Is_Well_Formed);
   begin
      Child_Arrays.Append (Item.Children, Child, Budget, Success);
   end Append_Child;

   procedure Finish_Prototype
     (Item    : in out Chunk;
      Budget  : in out Memory_Budget;
      Facts   : Prototype_Header;
      Success : out Boolean)
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Is_Well_Formed);
      New_Entry : constant Prototype_Entry :=
        (Facts          => Facts,
         Code_Base      => Item.Pending_Code,
         Code_Length    =>
           Natural (Instruction_Arrays.Length (Item.Instructions)) - Item.Pending_Code,
         Constant_Base  => Item.Pending_Constants,
         Constant_Count =>
           Natural (Constant_Arrays.Length (Item.Constants)) - Item.Pending_Constants,
         Upvalue_Base   => Item.Pending_Upvalues,
         Upvalue_Count  =>
           Natural (Upvalue_Arrays.Length (Item.Upvalues)) - Item.Pending_Upvalues,
         Local_Base     => Item.Pending_Locals,
         Local_Count    => Natural (Local_Arrays.Length (Item.Locals)) - Item.Pending_Locals,
         Child_Base     => Item.Pending_Children,
         Child_Count    =>
           Natural (Child_Arrays.Length (Item.Children)) - Item.Pending_Children);
      Old_Count : constant Prototype_Index := Prototype_Count (Item);
      Old_Model : constant Prototype_Arrays.Models.Sequence :=
        Prototype_Arrays.Model (Item.Prototypes)
      with Ghost;
      --  Entry E ends before the given marks.
      function Within (E : Prototype_Entry; Code, Constants, Upvalues, Locals, Children : Natural)
         return Boolean
      is (E.Code_Base + E.Code_Length <= Code
          and then E.Constant_Base + E.Constant_Count <= Constants
          and then E.Upvalue_Base + E.Upvalue_Count <= Upvalues
          and then E.Local_Base + E.Local_Count <= Locals
          and then E.Child_Base + E.Child_Count <= Children)
      with Ghost;
   begin
      pragma Assert
        (for all P in 1 .. Old_Count =>
           Within (Prototype_Arrays.Models.Get (Old_Model, P), Item.Pending_Code,
                   Item.Pending_Constants, Item.Pending_Upvalues, Item.Pending_Locals,
                   Item.Pending_Children));
      Prototype_Arrays.Append (Item.Prototypes, New_Entry, Budget, Success);
      --  The entries of the earlier prototypes are unchanged.
      pragma Assert
        (for all P in 1 .. Old_Count =>
           Prototype_Arrays.Element (Item.Prototypes, P)
           = Prototype_Arrays.Models.Get (Old_Model, P));
      if Success then
         Item.Pending_Code := Natural (Instruction_Arrays.Length (Item.Instructions));
         Item.Pending_Constants := Natural (Constant_Arrays.Length (Item.Constants));
         Item.Pending_Upvalues := Natural (Upvalue_Arrays.Length (Item.Upvalues));
         Item.Pending_Locals := Natural (Local_Arrays.Length (Item.Locals));
         Item.Pending_Children := Natural (Child_Arrays.Length (Item.Children));
      end if;
   end Finish_Prototype;

   procedure Validate (Item : in out Chunk; Budget : in out Memory_Budget; Valid : out Boolean)
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Is_Valid);
   begin
      Valid := Is_Valid (Item);
      if not Valid then
         Clear (Item, Budget);
      end if;
   end Validate;

   procedure Clear (Item : in out Chunk; Budget : in out Memory_Budget) is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Is_Well_Formed);
   begin
      Instruction_Arrays.Clear (Item.Instructions, Budget);
      Line_Arrays.Clear (Item.Lines, Budget);
      Constant_Arrays.Clear (Item.Constants, Budget);
      Upvalue_Arrays.Clear (Item.Upvalues, Budget);
      Local_Arrays.Clear (Item.Locals, Budget);
      Child_Arrays.Clear (Item.Children, Budget);
      Prototype_Arrays.Clear (Item.Prototypes, Budget);
      Item.Pending_Code := 0;
      Item.Pending_Constants := 0;
      Item.Pending_Upvalues := 0;
      Item.Pending_Locals := 0;
      Item.Pending_Children := 0;
   end Clear;

end Pyro.Bytecode;
