--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  Interned byte strings: names and string literals, each stored once and named by an index.

with Interfaces;
with Pyro.Character_Arrays;
with Pyro.Growable_Arrays;
with Pyro.Memory_Budgets; use Pyro.Memory_Budgets;

package Pyro.Symbols with SPARK_Mode => On, Always_Terminates is

   --  The most symbols a table holds.
   Maximum_Symbols : constant := 2 ** 28;

   --  A symbol in a table, or No_Symbol.
   type Symbol_Index is range 0 .. Maximum_Symbols;

   --  No symbol (an empty payload, or a failed interning).
   No_Symbol : constant Symbol_Index := 0;

   --  The length of a symbol's text.
   subtype Symbol_Length is Natural range 0 .. Natural (Byte_Position'Last);

   --  A set of byte strings. Interning the same bytes twice gives the same symbol, so symbols
   --  are equal exactly when their indices are. It owns heap memory: release it with Clear.
   type Symbol_Table is limited private
   with
     Default_Initial_Condition =>
       Is_Valid (Symbol_Table)
       and then Count (Symbol_Table) = 0
       and then Is_Released (Symbol_Table);

   --  The number of symbols in Table.
   function Count (Table : Symbol_Table) return Symbol_Index
   with Global => null;

   --  The table's internal references are consistent. Every operation keeps this true.
   function Is_Valid (Table : Symbol_Table) return Boolean
   with Global => null;

   --  The number of bytes of Symbol.
   function Length (Table : Symbol_Table; Symbol : Symbol_Index) return Symbol_Length
   with Global => null, Pre => Is_Valid (Table) and then Symbol in 1 .. Count (Table);

   --  The byte of Symbol at Position.
   function Element
     (Table : Symbol_Table; Symbol : Symbol_Index; Position : Positive) return Character
   with
     Global => null,
     Pre    =>
       Is_Valid (Table)
       and then Symbol in 1 .. Count (Table)
       and then Position <= Length (Table, Symbol);

   --  The bytes of Symbol.
   function Text (Table : Symbol_Table; Symbol : Symbol_Index) return String
   with
     Global => null,
     Pre    => Is_Valid (Table) and then Symbol in 1 .. Count (Table),
     Post   => Text'Result'First = 1 and then Text'Result'Length = Length (Table, Symbol);

   --  The symbol for Buffer (First .. Last), added to Table if it is new (First > Last is the
   --  empty string). Symbol is No_Symbol when the table is full or Budget cannot pay for the
   --  growth.
   procedure Intern
     (Table  : in out Symbol_Table;
      Budget : in out Memory_Budget;
      Buffer : Character_Arrays.Growable_Array;
      First  : Byte_Position;
      Last   : Character_Arrays.Extended_Index;
      Symbol : out Symbol_Index)
   with
     Global => null,
     Pre    =>
       Is_Valid (Table)
       and then Last <= Character_Arrays.Length (Buffer)
       and then (First <= Last or else First = Last + 1),
     Post   =>
       Is_Valid (Table)
       and then Count (Table) >= Count (Table)'Old
       and then Symbol <= Count (Table)
       and then Limit (Budget) = Limit (Budget)'Old;

   --  The symbol whose bytes are Text, or No_Symbol if Table does not hold it.
   function Find_Text (Table : Symbol_Table; Text : String) return Symbol_Index
   with
     Global => null,
     Pre    => Is_Valid (Table) and then Text'Length <= 4096,
     Post   => Find_Text'Result <= Count (Table);

   --  Exchanges the symbols (and memory) of Left and Right.
   procedure Swap (Left, Right : in out Symbol_Table)
   with
     Global => null,
     Pre    => Is_Valid (Left) and then Is_Valid (Right),
     Post   =>
       Is_Valid (Left)
       and then Is_Valid (Right)
       and then Count (Left) = Count (Right)'Old
       and then Count (Right) = Count (Left)'Old
       and then Is_Released (Left) = Is_Released (Right)'Old
       and then Is_Released (Right) = Is_Released (Left)'Old;

   --  Removes every symbol and releases the memory.
   procedure Clear (Table : in out Symbol_Table; Budget : in out Memory_Budget)
   with
     Global => null,
     Post   =>
       Is_Valid (Table)
       and then Count (Table) = 0
       and then Is_Released (Table)
       and then Limit (Budget) = Limit (Budget)'Old;

   --  True when the table holds no heap memory.
   function Is_Released (Table : Symbol_Table) return Boolean
   with Global => null;

private

   use type Interfaces.Unsigned_32;

   --  Where a symbol's bytes are in the table's text, and their hash.
   type Symbol_Entry is record
      First  : Byte_Position := 1;
      Length : Symbol_Length := 0;
      Hash   : Interfaces.Unsigned_32 := 0;
   end record;

   subtype Entry_Position is Symbol_Index range 1 .. Symbol_Index'Last;

   package Entry_Arrays is new Pyro.Growable_Arrays
     (Index => Entry_Position, Element_Type => Symbol_Entry,
      Default_Element => (First => 1, Length => 0, Hash => 0), Element_Bytes => 16);

   --  A slot of the hash table: a symbol, or No_Symbol for an empty slot.
   type Slot_Position is range 1 .. 2 ** 29;

   package Slot_Arrays is new Pyro.Growable_Arrays
     (Index => Slot_Position, Element_Type => Symbol_Index, Default_Element => No_Symbol,
      Element_Bytes => 4);

   type Symbol_Table is limited record
      Text    : Character_Arrays.Growable_Array;
      Entries : Entry_Arrays.Growable_Array;
      Slots   : Slot_Arrays.Growable_Array;
   end record;

   function Count (Table : Symbol_Table) return Symbol_Index
   is (Entry_Arrays.Length (Table.Entries));

   function Length (Table : Symbol_Table; Symbol : Symbol_Index) return Symbol_Length
   is (Entry_Arrays.Element (Table.Entries, Symbol).Length);

   function Is_Released (Table : Symbol_Table) return Boolean
   is (Character_Arrays.Is_Released (Table.Text)
       and then Entry_Arrays.Is_Released (Table.Entries)
       and then Slot_Arrays.Is_Released (Table.Slots));

end Pyro.Symbols;
