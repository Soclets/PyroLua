--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  Interned byte strings: names and string literals, each stored once and named by an index.

package body Pyro.Symbols with SPARK_Mode => On is

   --  The bytes of an entry lie inside the text.
   function Is_Stored (Item : Symbol_Entry; Text_Length : Character_Arrays.Extended_Index)
     return Boolean
   is (Natural (Item.First) - 1 + Item.Length <= Natural (Text_Length));

   function Is_Valid (Table : Symbol_Table) return Boolean
   is ((for all Position in 1 .. Entry_Arrays.Length (Table.Entries) =>
          Is_Stored (Entry_Arrays.Element (Table.Entries, Position),
                     Character_Arrays.Length (Table.Text)))
       and then (for all Slot in 1 .. Slot_Arrays.Length (Table.Slots) =>
                   Slot_Arrays.Element (Table.Slots, Slot) <= Count (Table)));

   --  Slots of the first hash table.
   Initial_Slots : constant := 64;

   --  [proof] Appending to the text keeps every entry inside it.
   procedure Lemma_Text_Grew
     (Table : Symbol_Table; Old_Length : Character_Arrays.Extended_Index)
   with
     Ghost,
     Global => null,
     Pre    =>
       Old_Length <= Character_Arrays.Length (Table.Text)
       and then (for all Position in 1 .. Entry_Arrays.Length (Table.Entries) =>
                   Is_Stored (Entry_Arrays.Element (Table.Entries, Position), Old_Length)),
     Post   =>
       (for all Position in 1 .. Entry_Arrays.Length (Table.Entries) =>
          Is_Stored (Entry_Arrays.Element (Table.Entries, Position),
                     Character_Arrays.Length (Table.Text)));

   procedure Lemma_Text_Grew
     (Table : Symbol_Table; Old_Length : Character_Arrays.Extended_Index) is null;

   function Element
     (Table : Symbol_Table; Symbol : Symbol_Index; Position : Positive) return Character
   is
      Item : constant Symbol_Entry := Entry_Arrays.Element (Table.Entries, Symbol);
   begin
      return Character_Arrays.Element
        (Table.Text, Item.First + Byte_Position'Base (Position) - 1);
   end Element;

   function Text (Table : Symbol_Table; Symbol : Symbol_Index) return String is
      Size   : constant Symbol_Length := Length (Table, Symbol);
      Result : String (1 .. Size);
   begin
      for Position in 1 .. Size loop
         pragma Loop_Invariant (Size = Length (Table, Symbol));
         Result (Position) := Element (Table, Symbol, Position);
      end loop;
      return Result;
   end Text;

   --  FNV-1a hash of Buffer (First .. Last).
   function Hash_Of
     (Buffer : Character_Arrays.Growable_Array;
      First  : Byte_Position;
      Last   : Character_Arrays.Extended_Index) return Interfaces.Unsigned_32
   with Pre => Last <= Character_Arrays.Length (Buffer)
   is
      Hash : Interfaces.Unsigned_32 := 2_166_136_261;
   begin
      for Position in First .. Last loop
         Hash := (Hash xor Character'Pos (Character_Arrays.Element (Buffer, Position)))
           * 16_777_619;
      end loop;
      return Hash;
   end Hash_Of;

   --  True when the entry Symbol holds the bytes Buffer (First .. Last).
   function Has_Text
     (Table  : Symbol_Table;
      Symbol : Symbol_Index;
      Buffer : Character_Arrays.Growable_Array;
      First  : Byte_Position;
      Last   : Character_Arrays.Extended_Index) return Boolean
   with
     Pre =>
       Is_Valid (Table)
       and then Symbol in 1 .. Count (Table)
       and then Last <= Character_Arrays.Length (Buffer)
       and then (First <= Last or else First = Last + 1)
   is
      Item : constant Symbol_Entry := Entry_Arrays.Element (Table.Entries, Symbol);
   begin
      if Natural (Last) - Natural (First) + 1 /= Item.Length then
         return False;
      end if;
      for Offset in 0 .. Item.Length - 1 loop
         if Character_Arrays.Element (Table.Text, Item.First + Byte_Position'Base (Offset))
           /= Character_Arrays.Element (Buffer, First + Byte_Position'Base (Offset))
         then
            return False;
         end if;
      end loop;
      return True;
   end Has_Text;

   --  Index of the first slot to probe for Hash in a table of Size slots.
   function Home_Slot (Hash : Interfaces.Unsigned_32; Size : Slot_Arrays.Extended_Index)
     return Slot_Position
   with Pre => Size >= 1, Post => Home_Slot'Result <= Size;

   function Home_Slot (Hash : Interfaces.Unsigned_32; Size : Slot_Arrays.Extended_Index)
     return Slot_Position
   is
      Folded : constant Natural := Natural (Hash mod 2 ** 30);
      Offset : constant Natural := Folded mod Natural (Size);
   begin
      return Slot_Position (Offset + 1);
   end Home_Slot;

   --  Puts Symbol into the first empty slot on its probe sequence, if there is one.
   procedure Place (Table : in out Symbol_Table; Symbol : Symbol_Index)
   with
     Pre  =>
       Is_Valid (Table)
       and then Symbol in 1 .. Count (Table)
       and then Slot_Arrays.Length (Table.Slots) >= 1,
     Post =>
       Is_Valid (Table)
       and then Count (Table) = Count (Table)'Old
       and then Slot_Arrays.Length (Table.Slots) = Slot_Arrays.Length (Table.Slots)'Old
       and then Character_Arrays.Length (Table.Text)
                = Character_Arrays.Length (Table.Text)'Old
   is
      Size : constant Slot_Position := Slot_Arrays.Length (Table.Slots);
      Slot : Slot_Position :=
        Home_Slot (Entry_Arrays.Element (Table.Entries, Symbol).Hash, Size);
   begin
      for Step in 1 .. Size loop
         pragma Loop_Invariant (Is_Valid (Table));
         pragma Loop_Invariant (Slot_Arrays.Length (Table.Slots) = Size);
         pragma Loop_Invariant (Slot <= Size);
         if Slot_Arrays.Element (Table.Slots, Slot) = No_Symbol then
            Slot_Arrays.Replace_Element (Table.Slots, Slot, Symbol);
            return;
         end if;
         Slot := (if Slot = Size then 1 else Slot + 1);
      end loop;
   end Place;

   --  Replaces the hash table with an empty one of New_Size slots and puts every symbol back.
   procedure Rebuild_Slots
     (Table    : in out Symbol_Table;
      Budget   : in out Memory_Budget;
      New_Size : Slot_Position;
      Success  : out Boolean)
   with
     Pre  => Is_Valid (Table),
     Post =>
       Is_Valid (Table)
       and then Count (Table) = Count (Table)'Old
       and then Character_Arrays.Length (Table.Text) = Character_Arrays.Length (Table.Text)'Old
       and then (if Success then Slot_Arrays.Length (Table.Slots) = New_Size)
       and then Limit (Budget) = Limit (Budget)'Old
   is
   begin
      Slot_Arrays.Truncate (Table.Slots, 0);
      for Slot in 1 .. New_Size loop
         Slot_Arrays.Append (Table.Slots, No_Symbol, Budget, Success);
         if not Success then
            Slot_Arrays.Truncate (Table.Slots, 0);
            return;
         end if;
         pragma Loop_Invariant (Slot_Arrays.Length (Table.Slots) = Slot);
         pragma Loop_Invariant
           (for all Earlier in 1 .. Slot => Slot_Arrays.Element (Table.Slots, Earlier) = No_Symbol);
         pragma Loop_Invariant (Is_Valid (Table));
         pragma Loop_Invariant (Count (Table) = Count (Table)'Loop_Entry);
         pragma Loop_Invariant
           (Character_Arrays.Length (Table.Text) = Character_Arrays.Length (Table.Text)'Loop_Entry);
         pragma Loop_Invariant (Limit (Budget) = Limit (Budget)'Loop_Entry);
      end loop;
      for Symbol in 1 .. Count (Table) loop
         Place (Table, Symbol);
         pragma Loop_Invariant (Is_Valid (Table));
         pragma Loop_Invariant (Count (Table) = Count (Table)'Loop_Entry);
         pragma Loop_Invariant (Slot_Arrays.Length (Table.Slots) = New_Size);
         pragma Loop_Invariant
           (Character_Arrays.Length (Table.Text) = Character_Arrays.Length (Table.Text)'Loop_Entry);
      end loop;
      Success := True;
   end Rebuild_Slots;

   --  Adds the bytes Buffer (First .. Last) as a new symbol (it must not be in the table).
   procedure Add_Entry
     (Table  : in out Symbol_Table;
      Budget : in out Memory_Budget;
      Buffer : Character_Arrays.Growable_Array;
      First  : Byte_Position;
      Last   : Character_Arrays.Extended_Index;
      Hash   : Interfaces.Unsigned_32;
      Symbol : out Symbol_Index)
   with
     Pre  =>
       Is_Valid (Table)
       and then Last <= Character_Arrays.Length (Buffer)
       and then (First <= Last or else First = Last + 1),
     Post =>
       Is_Valid (Table)
       and then Slot_Arrays.Length (Table.Slots) = Slot_Arrays.Length (Table.Slots)'Old
       and then Count (Table) >= Count (Table)'Old
       and then (if Symbol /= No_Symbol then Symbol = Count (Table))
       and then Limit (Budget) = Limit (Budget)'Old
   is
      Length     : constant Natural := Natural (Last) - Natural (First) + 1;
      Old_Length : constant Character_Arrays.Extended_Index :=
        Character_Arrays.Length (Table.Text);
      Item       : Symbol_Entry := (First => 1, Length => Length, Hash => Hash);
      Success    : Boolean;
   begin
      Symbol := No_Symbol;
      if Length > Natural (Byte_Position'Last) - Natural (Old_Length) then
         return;
      end if;
      if Length > 0 then
         Item.First := Old_Length + 1;
      end if;
      for Position in First .. Last loop
         Character_Arrays.Append
           (Table.Text, Character_Arrays.Element (Buffer, Position), Budget, Success);
         if not Success then
            Lemma_Text_Grew (Table, Old_Length);
            return;
         end if;
         pragma Loop_Invariant
           (Character_Arrays.Length (Table.Text)
            = Old_Length + (Position - First + 1));
         pragma Loop_Invariant
           (for all Earlier in 1 .. Entry_Arrays.Length (Table.Entries) =>
              Is_Stored (Entry_Arrays.Element (Table.Entries, Earlier), Old_Length));
         pragma Loop_Invariant
           (for all Slot in 1 .. Slot_Arrays.Length (Table.Slots) =>
              Slot_Arrays.Element (Table.Slots, Slot) <= Count (Table));
         pragma Loop_Invariant
           (Slot_Arrays.Length (Table.Slots) = Slot_Arrays.Length (Table.Slots)'Loop_Entry);
         pragma Loop_Invariant (Count (Table) = Count (Table)'Loop_Entry);
         pragma Loop_Invariant (Limit (Budget) = Limit (Budget)'Loop_Entry);
      end loop;
      Lemma_Text_Grew (Table, Old_Length);
      pragma Assert (Is_Stored (Item, Character_Arrays.Length (Table.Text)));
      Entry_Arrays.Append (Table.Entries, Item, Budget, Success);
      if Success then
         Symbol := Count (Table);
      end if;
   end Add_Entry;

   procedure Intern
     (Table  : in out Symbol_Table;
      Budget : in out Memory_Budget;
      Buffer : Character_Arrays.Growable_Array;
      First  : Byte_Position;
      Last   : Character_Arrays.Extended_Index;
      Symbol : out Symbol_Index)
   is
      Hash    : constant Interfaces.Unsigned_32 := Hash_Of (Buffer, First, Last);
      Size    : Slot_Arrays.Extended_Index := Slot_Arrays.Length (Table.Slots);
      Slot    : Slot_Position;
      Success : Boolean;
   begin
      Symbol := No_Symbol;
      if Count (Table) = Symbol_Index'Last then
         return;
      end if;
      --  Keep the table at most half full, so probe sequences stay short.
      if Size = 0 or else Slot_Arrays.Extended_Index (Count (Table)) + 1 > Size / 2 then
         if Size > Slot_Position'Last / 2 then
            return;
         end if;
         Rebuild_Slots (Table, Budget, Slot_Position'Max (Initial_Slots, 2 * Size), Success);
         if not Success then
            return;
         end if;
         Size := Slot_Arrays.Length (Table.Slots);
      end if;
      Slot := Home_Slot (Hash, Size);
      for Step in 1 .. Size loop
         pragma Loop_Invariant (Is_Valid (Table));
         pragma Loop_Invariant (Slot_Arrays.Length (Table.Slots) = Size);
         pragma Loop_Invariant (Slot <= Size);
         pragma Loop_Invariant (Count (Table) = Count (Table)'Loop_Entry);
         pragma Loop_Invariant (Limit (Budget) = Limit (Budget)'Loop_Entry);
         declare
            Occupant : constant Symbol_Index := Slot_Arrays.Element (Table.Slots, Slot);
         begin
            if Occupant = No_Symbol then
               Add_Entry (Table, Budget, Buffer, First, Last, Hash, Symbol);
               if Symbol /= No_Symbol then
                  Slot_Arrays.Replace_Element (Table.Slots, Slot, Symbol);
               end if;
               return;
            elsif Entry_Arrays.Element (Table.Entries, Occupant).Hash = Hash
              and then Has_Text (Table, Occupant, Buffer, First, Last)
            then
               Symbol := Occupant;
               return;
            end if;
         end;
         Slot := (if Slot = Size then 1 else Slot + 1);
      end loop;
   end Intern;

   function Find_Text (Table : Symbol_Table; Text : String) return Symbol_Index is
      Size : constant Slot_Arrays.Extended_Index := Slot_Arrays.Length (Table.Slots);
      Hash : Interfaces.Unsigned_32 := 2_166_136_261;
      Slot : Slot_Position;
   begin
      if Size = 0 then
         return No_Symbol;
      end if;
      for Byte of Text loop
         Hash := (Hash xor Character'Pos (Byte)) * 16_777_619;
      end loop;
      Slot := Home_Slot (Hash, Size);
      for Step in 1 .. Size loop
         pragma Loop_Invariant (Slot <= Size);
         declare
            Occupant : constant Symbol_Index := Slot_Arrays.Element (Table.Slots, Slot);
         begin
            if Occupant = No_Symbol then
               return No_Symbol;
            elsif Length (Table, Occupant) = Text'Length then
               declare
                  Same : Boolean := True;
               begin
                  for Offset in 0 .. Text'Length - 1 loop
                     if Element (Table, Occupant, Offset + 1) /= Text (Text'First + Offset) then
                        Same := False;
                        exit;
                     end if;
                  end loop;
                  if Same then
                     return Occupant;
                  end if;
               end;
            end if;
         end;
         Slot := (if Slot = Size then 1 else Slot + 1);
      end loop;
      return No_Symbol;
   end Find_Text;

   procedure Swap (Left, Right : in out Symbol_Table) is
   begin
      Character_Arrays.Swap (Left.Text, Right.Text);
      Entry_Arrays.Swap (Left.Entries, Right.Entries);
      Slot_Arrays.Swap (Left.Slots, Right.Slots);
   end Swap;

   procedure Clear (Table : in out Symbol_Table; Budget : in out Memory_Budget) is
   begin
      Character_Arrays.Clear (Table.Text, Budget);
      Entry_Arrays.Clear (Table.Entries, Budget);
      Slot_Arrays.Clear (Table.Slots, Budget);
   end Clear;

end Pyro.Symbols;
