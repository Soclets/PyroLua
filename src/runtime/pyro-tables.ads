--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  Lua tables: an array part for the integer keys 1 .. N, and a hash part with open
--  addressing for the other keys.

with Interfaces;          use Interfaces;
with Pyro.Memory_Budgets; use Pyro.Memory_Budgets;
with Pyro.Strings;
with Pyro.Value_Maps;
with Pyro.Value_Sequences;
with Pyro.Values;         use Pyro.Values;

package Pyro.Tables with SPARK_Mode => On, Always_Terminates is

   use type Pyro.Strings.Seed;
   use type Value_Maps.Map;

   --  The largest array part, and the most nodes of a hash part.
   Maximum_Array_Size : constant := 2 ** 26;
   Maximum_Capacity   : constant := 2 ** 26;

   --  The most values a table holds: its array part, then a key and a value for each node.
   Maximum_Entry_Count : constant := Maximum_Array_Size + 2 * Maximum_Capacity;

   --  Bytes charged for each place of the array part and each node of the hash part.
   Item_Bytes : constant Byte_Count := 16;
   Node_Bytes : constant Byte_Count := 48;

   --  A table. It owns heap memory: release it with Clear.
   type Table is limited private
   with
     Default_Initial_Condition =>
       Is_Valid (Table) and then Is_Released (Table) and then Is_Empty (Table),
     Annotate => (GNATprove, Ownership, "Needs_Reclamation");

   --  [proof] The table is well formed: every key of the hash part can be found along its
   --  probe sequence, no key is there twice, and no key of the array part is there.
   function Is_Valid (T : Table) return Boolean
   with Ghost, Global => null;

   --  True when the table holds no memory.
   function Is_Released (T : Table) return Boolean
   with Global => null, Annotate => (GNATprove, Ownership, "Is_Reclaimed");

   --  [proof] The contents: every key (as Key_Of gives it) with its value, never nil.
   function Model (T : Table) return Value_Maps.Map
   with Ghost, Global => null;

   --  [proof] The table has no keys.
   function Is_Empty (T : Table) return Boolean
   is (Value_Maps.Is_Empty (Model (T)))
   with Ghost;

   --  The key of the hashes of the table's keys.
   function Seed (T : Table) return Pyro.Strings.Seed
   with Global => null;

   --  Sets the key of the hashes, on a table that holds nothing yet.
   procedure Set_Seed (T : in out Table; Key : Pyro.Strings.Seed)
   with
     Global => null,
     Pre    => Is_Valid (T) and then Is_Released (T),
     Post   =>
       Is_Valid (T) and then Is_Released (T) and then Is_Empty (T) and then Seed (T) = Key;

   --  [proof] After is Before with Key bound to Item, or with Key absent when Item is nil.
   function Stored (After, Before : Value_Maps.Map; Key, Item : Value) return Boolean
   is ((if Item = Nil then not Value_Maps.Has_Key (After, Key)
        else Value_Maps.Has_Key (After, Key) and then Value_Maps.Get (After, Key) = Item)
       and then (for all Other of After =>
                   (if Other /= Key
                    then Value_Maps.Has_Key (Before, Other)
                         and then Value_Maps.Get (Before, Other) = Value_Maps.Get (After, Other)))
       and then (for all Other of Before =>
                   (if Other /= Key then Value_Maps.Has_Key (After, Other))))
   with Ghost;

   --  [puc ltable.c:luaH_get] The value of Key: nil when the table has no such key, and when
   --  Key cannot be a key (nil, NaN).
   function Get (T : Table; Key : Value) return Value
   with
     Global => null,
     Pre    => Is_Valid (T) and then Is_Canonical (Key),
     Post   =>
       Is_Canonical (Get'Result)
       and then Get'Result
                = (if Key_Of (Key) /= Nil and then Value_Maps.Has_Key (Model (T), Key_Of (Key))
                   then Value_Maps.Get (Model (T), Key_Of (Key))
                   else Nil);

   type Set_Status is
     (Done,           --  Key is bound to Item, or absent when Item is nil
      Invalid_Key,    --  Key is nil or NaN: "index is nil" / "index is NaN"
      Out_Of_Memory); --  the table needed to grow and Budget could not pay

   --  [puc ltable.c:luaH_set, luaH_newkey] Binds Key (as Key_Of gives it) to Item; a nil Item
   --  removes the key. A new key may rehash the table first, which resizes both parts as
   --  PUC Lua does. When it cannot grow, the table is unchanged.
   procedure Set
     (T      : in out Table;
      Budget : in out Memory_Budget;
      Key    : Value;
      Item   : Value;
      Status : out Set_Status)
   with
     Global => null,
     Pre    => Is_Valid (T) and then Is_Canonical (Key) and then Is_Canonical (Item),
     Post   =>
       Is_Valid (T)
       and then Seed (T) = Seed (T)'Old
       and then Limit (Budget) = Limit (Budget)'Old
       and then Entries_From (Entries (T), Entries (T)'Old, Key_Of (Key), Item)
       and then (case Status is
                   when Done          =>
                     Key_Of (Key) /= Nil
                     and then Stored (Model (T), Model (T)'Old, Key_Of (Key), Item),
                   when Invalid_Key   => Key_Of (Key) = Nil and then Model (T) = Model (T)'Old,
                   when Out_Of_Memory => Model (T) = Model (T)'Old);

   --  [puc ltable.c:luaH_resize] Resizes the array part to Array_Size places and the hash part
   --  to room for Hash_Size keys, keeping every key. Success is False, and the table
   --  unchanged, when Budget cannot pay or the keys do not fit.
   procedure Resize
     (T          : in out Table;
      Budget     : in out Memory_Budget;
      Array_Size : Natural;
      Hash_Size  : Natural;
      Success    : out Boolean)
   with
     Global => null,
     Pre    =>
       Is_Valid (T) and then Array_Size <= Maximum_Array_Size
       and then Hash_Size <= Maximum_Capacity / 2,
     Post   =>
       Is_Valid (T)
       and then Seed (T) = Seed (T)'Old
       and then Limit (Budget) = Limit (Budget)'Old
       and then Model (T) = Model (T)'Old
       and then Entries_From (Entries (T), Entries (T)'Old, Nil, Nil);

   --  The places of the array part, and the keys the hash part has room for as Resize sizes
   --  it: what luaH_realasize and allocsizenode give, so that Resize can grow one part and
   --  keep the other.
   function Array_Size (T : Table) return Natural
   with Global => null, Post => Array_Size'Result <= Maximum_Array_Size;

   function Hash_Room (T : Table) return Natural
   with Global => null, Post => Hash_Room'Result <= Maximum_Capacity / 2;

   type Next_Status is
     (Found,          --  Next_Key and Next_Item are the next key and its value
      Finished,       --  Key was the last key (or nil, on an empty table)
      Invalid_Key);   --  Key is not in the table: "invalid key to 'next'"

   --  [puc ltable.c:luaH_next] The key after Key in the table's order, nil Key for the first:
   --  the array part in order, then the hash part. A key removed (set to nil) during the
   --  traversal is still found, so the traversal goes on.
   procedure Next
     (T         : Table;
      Key       : Value;
      Next_Key  : out Value;
      Next_Item : out Value;
      Status    : out Next_Status)
   with
     Global => null,
     Pre    => Is_Valid (T) and then Is_Canonical (Key),
     Post   =>
       Is_Canonical (Next_Key)
       and then Is_Canonical (Next_Item)
       and then (if Status = Found
                 then Value_Maps.Has_Key (Model (T), Next_Key)
                      and then Value_Maps.Get (Model (T), Next_Key) = Next_Item
                 else Next_Key = Nil and then Next_Item = Nil);

   --  [puc ltable.c:luaH_getn] A border of the table: 0 when t[1] is nil, or N with t[N] not
   --  nil and t[N + 1] nil. Found as PUC Lua finds it, so it is the border PUC Lua gives in
   --  practice (any border is a valid length when the sequence has holes).
   function Length (T : Table) return Integer_64
   with
     Global => null,
     Pre    => Is_Valid (T),
     Post   =>
       Length'Result >= 0
       and then (Length'Result = 0
                 or else Value_Maps.Has_Key (Model (T), Integer_Value_Of (Length'Result)))
       and then (Length'Result = Integer_64'Last
                 or else not Value_Maps.Has_Key
                               (Model (T), Integer_Value_Of (Length'Result + 1)));

   --  Removes every key and releases the table's memory from Budget.
   procedure Clear (T : in out Table; Budget : in out Memory_Budget)
   with
     Global => null,
     Post   =>
       Is_Valid (T)
       and then Is_Released (T)
       and then Is_Empty (T)
       and then Seed (T) = Seed (T)'Old
       and then Limit (Budget) = Limit (Budget)'Old;

   --  The values the table holds, for the collector: the array part, then each node's key
   --  and value. A place with nothing holds nil. A removed key is still held (until the table
   --  is rehashed), so that the traversal can go on past it.
   function Entry_Count (T : Table) return Natural
   with Global => null, Post => Entry_Count'Result <= Maximum_Entry_Count;

   function Entry_At (T : Table; Position : Positive) return Value
   with Global => null, Pre => Position <= Entry_Count (T);

   --  [proof] The values the table holds.
   function Entries (T : Table) return Value_Sequences.Sequence
   with
     Ghost,
     Global => null,
     Post   =>
       Value_Sequences.Last (Entries'Result) = Entry_Count (T)
       and then (for all Position in 1 .. Entry_Count (T) =>
                   Value_Sequences.Get (Entries'Result, Position) = Entry_At (T, Position))
       and then (if Is_Released (T) then Value_Sequences.Last (Entries'Result) = 0);

   --  [proof] The value of every key is among the table's entries, and so is the key when it
   --  is an object: what the heap needs to know that what a table gives refers to live
   --  objects.
   procedure Lemma_Model_In_Entries (T : Table; Key : Value)
   with
     Ghost,
     Global => null,
     Pre    => Is_Valid (T) and then Value_Maps.Has_Key (Model (T), Key),
     Post   =>
       (Key.Kind /= Object_Value
        or else Value_Sequences.Contains
                  (Entries (T), 1, Value_Sequences.Last (Entries (T)), Key))
       and then Value_Sequences.Contains
                  (Entries (T), 1, Value_Sequences.Last (Entries (T)),
                   Value_Maps.Get (Model (T), Key));

   --  [proof] Every object After holds is Key, Item, or an object Before holds: what the heap
   --  needs to know that a table refers only to live objects.
   function Entries_From (After, Before : Value_Sequences.Sequence; Key, Item : Value)
     return Boolean
   is (for all Position in 1 .. Value_Sequences.Last (After) =>
         Value_Sequences.Get (After, Position).Kind /= Object_Value
         or else Value_Sequences.Get (After, Position) = Key
         or else Value_Sequences.Get (After, Position) = Item
         or else Value_Sequences.Contains
                   (Before, 1, Value_Sequences.Last (Before),
                    Value_Sequences.Get (After, Position)))
   with Ghost;

   --  The longest probe sequence of the hash part (0 when every key is at its home node): what
   --  a lookup can cost, for the tests of hostile keys.
   function Longest_Probe (T : Table) return Natural
   with Global => null;

private
   --  Clients see the table through the operations above, which keeps its representation
   --  (two owned arrays) out of their proofs.
   pragma Annotate (GNATprove, Hide_Info, "Private_Part");

   type Value_Array is array (Positive range <>) of Value;
   type Value_Array_Access is access Value_Array;

   --  A node of the hash part: empty, used by a key and its value, or dead (its key was
   --  removed, and is kept so that a traversal can go on past it, and probes past it).
   type Node_State is (Empty_Node, Used_Node, Dead_Node);

   type Node is record
      State : Node_State := Empty_Node;
      Key   : Value := Nil;
      --  The hash of Key.
      Hash  : Unsigned_64 := 0;
      Item  : Value := Nil;
   end record;

   subtype Node_Index is Natural range 0 .. Maximum_Capacity - 1;
   type Node_Array is array (Node_Index range <>) of Node;
   type Node_Array_Access is access Node_Array;

   type Table is limited record
      Seed   : Pyro.Strings.Seed;
      Items  : Value_Array_Access := null;
      Nodes  : Node_Array_Access := null;
      --  Used and dead nodes: when to rehash. A new key goes to the hash part only while it is
      --  below three quarters of the nodes, so it finds a free one. The proofs do not rely on
      --  it: a full hash part makes Set report Out_Of_Memory, never break the table.
      Filled : Natural := 0;
   end record;

   function Seed (T : Table) return Pyro.Strings.Seed
   is (T.Seed);

   function Array_Size (T : Table) return Natural
   is (if T.Items = null then 0 else Natural'Min (T.Items'Length, Maximum_Array_Size));

   --  The most keys for which Resize gives the hash part as many nodes as it has.
   function Hash_Room (T : Table) return Natural
   is (if T.Nodes = null or else T.Nodes'Length < 4 then 0
       else Natural'Min (T.Nodes'Length / 2 - 1, Maximum_Capacity / 2));

   function Is_Released (T : Table) return Boolean
   is (T.Items = null and then T.Nodes = null);

end Pyro.Tables;
