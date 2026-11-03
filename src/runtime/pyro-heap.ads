--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  The heap: numbered slots holding Lua's objects, reached by handles.

with Interfaces;          use Interfaces;
with Pyro.Color_Sequences;
with Pyro.Graph_Sequences;
with Pyro.Kind_Sequences;
with Pyro.Memory_Budgets; use Pyro.Memory_Budgets;
with Pyro.Strings;
with Pyro.Tables;
with Pyro.Value_Maps;
with Pyro.Value_Sequences;
with Pyro.Values;         use Pyro.Values;

package Pyro.Heap with SPARK_Mode => On, Always_Terminates is

   use type Pyro.Strings.Seed;
   use type Color_Sequences.Sequence;
   use type Graph_Sequences.Sequence;
   use type Kind_Sequences.Sequence;
   use type Value_Maps.Map;
   use type Value_Sequences.Sequence;

   --  The longest string, in bytes.
   Maximum_String_Length : constant := Pyro.Strings.Maximum_String_Length;

   --  The bytes of a string.
   subtype Byte_Array is Pyro.Strings.Byte_Array;

   --  Bytes charged to the memory budget for each object, besides its contents.
   Object_Overhead : constant Byte_Count := 32;

   --  The objects of a Lua state. It owns heap memory: release it with Clear.
   type Heap is limited private
   with
     Default_Initial_Condition =>
       Is_Valid (Heap) and then Slot_Count (Heap) = 0 and then Is_Released (Heap),
     Annotate => (GNATprove, Ownership, "Needs_Reclamation");

   --  The number of slots, free or holding an object: the handles are 1 .. Slot_Count.
   function Slot_Count (H : Heap) return Object_Handle
   with Global => null;

   --  What slot Handle holds: Free_Object for No_Object and for handles past Slot_Count.
   function Kind_Of (H : Heap; Handle : Object_Handle) return Object_Kind
   with
     Global => null,
     Post   =>
       (if Handle = No_Object or else Handle > Slot_Count (H)
        then Kind_Of'Result = Free_Object);

   --  [proof] The kind of every slot.
   function Kinds (H : Heap) return Kind_Sequences.Sequence
   with
     Ghost,
     Global => null,
     Post   =>
       Kind_Sequences.Last (Kinds'Result) = Slot_Count (H)
       and then (for all Handle in 1 .. Slot_Count (H) =>
                   Kind_Sequences.Get (Kinds'Result, Handle) = Kind_Of (H, Handle));

   --  [proof] Every slot that Before shows holding an object holds an object of the same kind
   --  in After: what allocation preserves.
   function Keeps_Objects (Before, After : Kind_Sequences.Sequence) return Boolean
   is (Kind_Sequences.Last (Before) <= Kind_Sequences.Last (After)
       and then (for all Handle in 1 .. Kind_Sequences.Last (Before) =>
                   (if Kind_Sequences.Get (Before, Handle) /= Free_Object
                    then Kind_Sequences.Get (After, Handle) = Kind_Sequences.Get (Before, Handle))))
   with Ghost;

   --  [proof] Item refers to no object, or to one that K shows holding an object.
   function Live_In (K : Kind_Sequences.Sequence; Item : Value) return Boolean
   is (Item.Kind /= Object_Value
       or else (Item.Object in 1 .. Kind_Sequences.Last (K)
                and then Kind_Sequences.Get (K, Item.Object) /= Free_Object))
   with Ghost;

   --  [proof] Item refers to no object, or to one the heap holds.
   function Is_Live (H : Heap; Item : Value) return Boolean
   is (Item.Kind /= Object_Value or else Kind_Of (H, Item.Object) /= Free_Object)
   with Ghost;

   --  The most values an object refers to besides a table's entries (Reference_Count): a
   --  closure's upvalues, at most lopcodes.h's MAXUPVAL.
   Maximum_References : constant := 255;

   --  [proof] The values object Handle holds: a table's entries (Pyro.Tables.Entries), then
   --  its references (Reference_At); nothing for a free slot or a string.
   function Children (H : Heap; Handle : Valid_Handle) return Value_Sequences.Sequence
   with
     Ghost,
     Global => null,
     Post   =>
       (if Kind_Of (H, Handle) in Free_Object | String_Object
        then Value_Sequences.Last (Children'Result) = 0);

   --  [proof] The children of every slot, by handle: the graph the collector walks.
   function Graph (H : Heap) return Graph_Sequences.Sequence
   with
     Ghost,
     Global => null,
     Post   =>
       Graph_Sequences.Last (Graph'Result) = Slot_Count (H)
       and then (for all Handle in 1 .. Slot_Count (H) =>
                   Graph_Sequences.Get (Graph'Result, Handle) = Children (H, Handle));

   --  [proof] Every value in G refers to an object K shows: what Is_Valid says of the
   --  objects tables refer to.
   function Graph_Live (K : Kind_Sequences.Sequence; G : Graph_Sequences.Sequence)
     return Boolean
   is (for all Handle in 1 .. Graph_Sequences.Last (G) =>
         (for all Position in 1 .. Value_Sequences.Last (Graph_Sequences.Get (G, Handle)) =>
            Live_In (K, Value_Sequences.Get (Graph_Sequences.Get (G, Handle), Position))))
   with Ghost;

   --  [proof] Every slot is either free and empty or holds one object of its kind, and every
   --  handle stored in an object refers to an object.
   function Is_Valid (H : Heap) return Boolean
   with Ghost, Global => null;

   --  [proof] In a valid heap, every value an object holds refers to an object.
   procedure Lemma_Graph_Live (H : Heap)
   with
     Ghost,
     Global => null,
     Pre    => Is_Valid (H),
     Post   => Graph_Live (Kinds (H), Graph (H));

   --  True when the heap holds no memory.
   function Is_Released (H : Heap) return Boolean
   with Global => null, Annotate => (GNATprove, Ownership, "Is_Reclaimed");

   --  Sets the key of the heap's hashes. The pyrolua program and hosts give a random one.
   procedure Set_Seed (H : in out Heap; Key : Pyro.Strings.Seed)
   with
     Global => null,
     Pre    => Is_Valid (H) and then Slot_Count (H) = 0,
     Post   => Is_Valid (H) and then Slot_Count (H) = 0 and then Seed (H) = Key;

   --  The key of the heap's hashes.
   function Seed (H : Heap) return Pyro.Strings.Seed
   with Global => null;

   --  The string holding the bytes of Text: the one that exists already (strings are
   --  interned, so two strings are equal exactly when their handles are), or a new one.
   --  No_Object (and the heap keeps its objects) when Budget cannot pay for it or every
   --  handle is in use.
   procedure New_String
     (H      : in out Heap;
      Budget : in out Memory_Budget;
      Text   : Byte_Array;
      Result : out Object_Handle)
   with
     Global => null,
     Pre    => Is_Valid (H) and then Text'Length <= Maximum_String_Length,
     Post   =>
       Is_Valid (H)
       and then Limit (Budget) = Limit (Budget)'Old
       and then Keeps_Objects (Kinds (H)'Old, Kinds (H))
       and then Seed (H) = Seed (H)'Old
       and then (if Result /= No_Object
                 then Kind_Of (H, Result) = String_Object
                      and then String_Length (H, Result) = Text'Length
                      and then (for all Position in 1 .. Text'Length =>
                                  String_Byte (H, Result, Byte_Position (Position))
                                  = Text (Text'First - 1 + Byte_Position (Position))));

   --  The hash of string S (Pyro.Strings.Hash of its bytes under the heap's seed).
   function String_Hash (H : Heap; S : Object_Handle) return Unsigned_64
   with Global => null, Pre => Kind_Of (H, S) = String_Object;

   --  The length of string S.
   function String_Length (H : Heap; S : Object_Handle) return Natural
   with Global => null, Pre => Kind_Of (H, S) = String_Object;

   --  Byte Position of string S.
   function String_Byte (H : Heap; S : Object_Handle; Position : Byte_Position) return Character
   with
     Global => null,
     Pre    => Kind_Of (H, S) = String_Object and then Natural (Position) <= String_Length (H, S);

   --  A new empty table. No_Object (and the heap keeps its objects) when Budget cannot pay
   --  for it or every handle is in use.
   procedure New_Table
     (H      : in out Heap;
      Budget : in out Memory_Budget;
      Result : out Object_Handle)
   with
     Global => null,
     Pre    => Is_Valid (H),
     Post   =>
       Is_Valid (H)
       and then Limit (Budget) = Limit (Budget)'Old
       and then Keeps_Objects (Kinds (H)'Old, Kinds (H))
       and then Seed (H) = Seed (H)'Old
       and then (if Result /= No_Object
                 then Kind_Of (H, Result) = Table_Object
                      and then Value_Maps.Is_Empty (Table_Model (H, Result))
                      and then Reference_Count (H, Result) = 1
                      and then Reference_At (H, Result, 1) = Nil);

   --  [proof] The contents of table T (Pyro.Tables.Model).
   function Table_Model (H : Heap; T : Valid_Handle) return Value_Maps.Map
   with Ghost, Global => null, Pre => Kind_Of (H, T) = Table_Object;

   --  The value of Key in table T (Pyro.Tables.Get).
   function Table_Get (H : Heap; T : Valid_Handle; Key : Value) return Value
   with
     Global => null,
     Pre    => Is_Valid (H) and then Kind_Of (H, T) = Table_Object and then Is_Canonical (Key),
     Post   =>
       Is_Canonical (Table_Get'Result)
       and then Is_Live (H, Table_Get'Result)
       and then Table_Get'Result
                = (if Key_Of (Key) /= Nil
                      and then Value_Maps.Has_Key (Table_Model (H, T), Key_Of (Key))
                   then Value_Maps.Get (Table_Model (H, T), Key_Of (Key))
                   else Nil);

   --  Binds Key to Item in table T (Pyro.Tables.Set). Key and Item must refer to objects
   --  the heap holds.
   procedure Table_Set
     (H      : in out Heap;
      Budget : in out Memory_Budget;
      T      : Valid_Handle;
      Key    : Value;
      Item   : Value;
      Status : out Pyro.Tables.Set_Status)
   with
     Global => null,
     Pre    =>
       Is_Valid (H)
       and then Kind_Of (H, T) = Table_Object
       and then Is_Canonical (Key) and then Is_Live (H, Key)
       and then Is_Canonical (Item) and then Is_Live (H, Item),
     Post   =>
       Is_Valid (H)
       and then Limit (Budget) = Limit (Budget)'Old
       and then Kinds (H) = Kinds (H)'Old
       and then Seed (H) = Seed (H)'Old
       and then (case Status is
                   when Pyro.Tables.Done          =>
                     Key_Of (Key) /= Nil
                     and then Pyro.Tables.Stored
                                (Table_Model (H, T), Table_Model (H, T)'Old, Key_Of (Key), Item),
                   when Pyro.Tables.Invalid_Key   =>
                     Key_Of (Key) = Nil and then Table_Model (H, T) = Table_Model (H, T)'Old,
                   when Pyro.Tables.Out_Of_Memory =>
                     Table_Model (H, T) = Table_Model (H, T)'Old);

   --  The collector's colour of object Handle: White for every free slot, and for every
   --  object outside a collection.
   function Color_Of (H : Heap; Handle : Object_Handle) return Object_Color
   with Global => null;

   --  [proof] The colour of every slot.
   function Colors (H : Heap) return Color_Sequences.Sequence
   with
     Ghost,
     Global => null,
     Post   =>
       Color_Sequences.Last (Colors'Result) = Slot_Count (H)
       and then (for all Handle in 1 .. Slot_Count (H) =>
                   Color_Sequences.Get (Colors'Result, Handle) = Color_Of (H, Handle));

   --  [proof] Every child of an object C does not show white is an object C does not show
   --  white: what sweeping needs so that no object it keeps refers to one it frees.
   function Closed (C : Color_Sequences.Sequence; G : Graph_Sequences.Sequence) return Boolean
   is (for all Handle in 1 .. Graph_Sequences.Last (G) =>
         (if Handle <= Color_Sequences.Last (C) and then Color_Sequences.Get (C, Handle) /= White
          then (for all Position in 1 .. Value_Sequences.Last (Graph_Sequences.Get (G, Handle)) =>
                  Value_Sequences.Get (Graph_Sequences.Get (G, Handle), Position).Kind
                  /= Object_Value
                  or else
                    (Value_Sequences.Get (Graph_Sequences.Get (G, Handle), Position).Object
                     in 1 .. Color_Sequences.Last (C)
                     and then Color_Sequences.Get
                                (C, Value_Sequences.Get
                                      (Graph_Sequences.Get (G, Handle), Position).Object)
                              /= White))))
   with Ghost;

   --  The number of values object Handle holds (Children), and the Position-th one.
   function Child_Count (H : Heap; Handle : Valid_Handle) return Natural
   with
     Global => null,
     Post   => Child_Count'Result = Value_Sequences.Last (Children (H, Handle));

   function Child_At (H : Heap; Handle : Valid_Handle; Position : Positive) return Value
   with
     Global => null,
     Pre    => Is_Valid (H) and then Position <= Child_Count (H, Handle),
     Post   =>
       Child_At'Result = Value_Sequences.Get (Children (H, Handle), Position)
       and then Is_Live (H, Child_At'Result);

   --  Makes white object Handle gray, and puts it on the gray list; a gray or black object
   --  stays as it is.
   procedure Shade (H : in out Heap; Handle : Valid_Handle)
   with
     Global => null,
     Pre    => Is_Valid (H) and then Kind_Of (H, Handle) /= Free_Object,
     Post   =>
       Is_Valid (H)
       and then Kinds (H) = Kinds (H)'Old
       and then Graph (H) = Graph (H)'Old
       and then Color_Of (H, Handle)
                = (if Color_Sequences.Get (Colors (H)'Old, Handle) = White then Gray
                   else Color_Sequences.Get (Colors (H)'Old, Handle))
       and then (for all Other in 1 .. Slot_Count (H) =>
                   (if Other /= Handle
                    then Color_Of (H, Other) = Color_Sequences.Get (Colors (H)'Old, Other)));

   --  The next object of the gray list, taken off it: a gray object, or No_Object when the
   --  list is empty (or names an object that is not gray, which ends it).
   procedure Take_Gray (H : in out Heap; Handle : out Object_Handle)
   with
     Global => null,
     Pre    => Is_Valid (H),
     Post   =>
       Is_Valid (H)
       and then Kinds (H) = Kinds (H)'Old
       and then Graph (H) = Graph (H)'Old
       and then Colors (H) = Colors (H)'Old
       and then (if Handle /= No_Object
                 then Handle <= Slot_Count (H)
                      and then Kind_Of (H, Handle) /= Free_Object
                      and then Color_Of (H, Handle) = Gray);

   --  Makes object Handle black.
   procedure Blacken (H : in out Heap; Handle : Valid_Handle)
   with
     Global => null,
     Pre    => Is_Valid (H) and then Kind_Of (H, Handle) /= Free_Object,
     Post   =>
       Is_Valid (H)
       and then Kinds (H) = Kinds (H)'Old
       and then Graph (H) = Graph (H)'Old
       and then Color_Of (H, Handle) = Black
       and then (for all Other in 1 .. Slot_Count (H) =>
                   (if Other /= Handle
                    then Color_Of (H, Other) = Color_Sequences.Get (Colors (H)'Old, Other)));

   --  Makes every object white and empties the gray list.
   procedure Whiten (H : in out Heap)
   with
     Global => null,
     Pre    => Is_Valid (H),
     Post   =>
       Is_Valid (H)
       and then Kinds (H) = Kinds (H)'Old
       and then Graph (H) = Graph (H)'Old
       and then (for all Handle in 1 .. Slot_Count (H) => Color_Of (H, Handle) = White);

   --  [puc lgc.c:sweeplist] Frees every white object, takes freed strings out of the intern
   --  set, releases their memory from Budget, and makes every object white. The objects that
   --  are not white must refer only to objects that are not white (Closed), so that no object
   --  kept refers to one freed.
   procedure Sweep (H : in out Heap; Budget : in out Memory_Budget)
   with
     Global => null,
     Pre    => Is_Valid (H) and then Closed (Colors (H), Graph (H)),
     Post   =>
       Is_Valid (H)
       and then Limit (Budget) = Limit (Budget)'Old
       and then Seed (H) = Seed (H)'Old
       and then Slot_Count (H) = Slot_Count (H)'Old
       and then (for all Handle in 1 .. Slot_Count (H) =>
                   Kind_Of (H, Handle)
                   = (if Color_Sequences.Get (Colors (H)'Old, Handle) = White then Free_Object
                      else Kind_Sequences.Get (Kinds (H)'Old, Handle)))
       and then (for all Handle in 1 .. Slot_Count (H) =>
                   (if Color_Sequences.Get (Colors (H)'Old, Handle) /= White
                    then Children (H, Handle) = Graph_Sequences.Get (Graph (H)'Old, Handle)))
       and then (for all Handle in 1 .. Slot_Count (H) => Color_Of (H, Handle) = White);

   --  The number of values object Handle refers to besides a table's entries: one for a
   --  table (its metatable, nil for none) and for an upvalue (its value once closed), a
   --  closure's upvalues, none for strings and host functions.
   function Reference_Count (H : Heap; Handle : Valid_Handle) return Natural
   with Global => null, Post => Reference_Count'Result <= Maximum_References;

   --  Reference Position of object Handle.
   function Reference_At (H : Heap; Handle : Valid_Handle; Position : Positive) return Value
   with Global => null, Pre => Position <= Reference_Count (H, Handle);

   --  [proof] In a valid heap, a reference is canonical and refers to an object the heap holds.
   procedure Lemma_Reference_Live (H : Heap; Handle : Valid_Handle; Position : Positive)
   with
     Ghost,
     Global => null,
     Pre    => Is_Valid (H) and then Position <= Reference_Count (H, Handle),
     Post   =>
       Is_Canonical (Reference_At (H, Handle, Position))
       and then Is_Live (H, Reference_At (H, Handle, Position));

   --  Makes reference Position of object Handle Item, which must refer to an object the heap
   --  holds.
   procedure Set_Reference
     (H : in out Heap; Handle : Valid_Handle; Position : Positive; Item : Value)
   with
     Global => null,
     Pre    =>
       Is_Valid (H)
       and then Kind_Of (H, Handle) /= Free_Object
       and then Position <= Reference_Count (H, Handle)
       and then Is_Canonical (Item)
       and then Is_Live (H, Item),
     Post   =>
       Is_Valid (H)
       and then Kinds (H) = Kinds (H)'Old
       and then Slot_Count (H) = Slot_Count (H)'Old
       and then Seed (H) = Seed (H)'Old
       and then Reference_Count (H, Handle) = Reference_Count (H, Handle)'Old
       and then Tag_Of (H, Handle) = Tag_Of (H, Handle)'Old
       and then Reference_At (H, Handle, Position) = Item;

   --  The number the VM keeps in object Handle: a closure's prototype, an open upvalue's place
   --  in the stack, a host function's number.
   function Tag_Of (H : Heap; Handle : Valid_Handle) return Natural
   with Global => null;

   --  Makes the number of object Handle Tag.
   procedure Set_Tag (H : in out Heap; Handle : Valid_Handle; Tag : Natural)
   with
     Global => null,
     Pre    => Is_Valid (H) and then Kind_Of (H, Handle) /= Free_Object,
     Post   =>
       Is_Valid (H)
       and then Kinds (H) = Kinds (H)'Old
       and then Slot_Count (H) = Slot_Count (H)'Old
       and then Seed (H) = Seed (H)'Old
       and then Reference_Count (H, Handle) = Reference_Count (H, Handle)'Old
       and then Tag_Of (H, Handle) = Tag;

   --  A new closure, upvalue or host function with number Tag and References references, all
   --  nil. No_Object (and the heap keeps its objects) when Budget cannot pay for it or every
   --  handle is in use.
   procedure New_Object
     (H          : in out Heap;
      Budget     : in out Memory_Budget;
      Kind       : Object_Kind;
      Tag        : Natural;
      References : Natural;
      Result     : out Object_Handle)
   with
     Global => null,
     Pre    =>
       Is_Valid (H)
       and then Kind in Closure_Object | Upvalue_Object | Host_Function_Object
       and then References <= Maximum_References,
     Post   =>
       Is_Valid (H)
       and then Limit (Budget) = Limit (Budget)'Old
       and then Keeps_Objects (Kinds (H)'Old, Kinds (H))
       and then Seed (H) = Seed (H)'Old
       and then (if Result /= No_Object
                 then Kind_Of (H, Result) = Kind
                      and then Tag_Of (H, Result) = Tag
                      and then Reference_Count (H, Result) = References
                      and then (for all Position in 1 .. References =>
                                  Reference_At (H, Result, Position) = Nil));

   --  Frees every object and releases the heap's memory from Budget.
   procedure Clear (H : in out Heap; Budget : in out Memory_Budget)
   with
     Global => null,
     Post   =>
       Is_Valid (H)
       and then Is_Released (H)
       and then Slot_Count (H) = 0
       and then Limit (Budget) = Limit (Budget)'Old;

private
   --  Clients see the heap through the operations above, which keeps its representation
   --  (a chunked store of slots owning their objects) out of their proofs.
   pragma Annotate (GNATprove, Hide_Info, "Private_Part");

   type Byte_Array_Access is access Byte_Array;
   type Table_Access is access Pyro.Tables.Table;

   --  The values an object refers to besides a table's entries.
   type Reference_Array is array (Positive range <>) of Value;
   type Reference_Array_Access is access Reference_Array;

   --  Bytes charged for each reference.
   Reference_Bytes : constant Byte_Count := 16;

   --  A slot: what it holds, and what it owns. A free slot links to the next free one, and a
   --  gray object to the next gray one; a string slot keeps its hash.
   type Slot is record
      Kind  : Object_Kind := Free_Object;
      Color : Object_Color := White;
      Link  : Object_Handle := No_Object;
      Hash  : Unsigned_64 := 0;
      Tag   : Natural := 0;
      Bytes : Byte_Array_Access := null;
      Table : Table_Access := null;
      Refs  : Reference_Array_Access := null;
   end record;

   --  Slots live in chunks of Chunk_Length, found through a table of Chunk_Count entries
   --  allocated once: a chunk is never copied, so the objects its slots own never move.
   Chunk_Length : constant := 2 ** 12;
   Chunk_Count  : constant := (Maximum_Objects + 1) / Chunk_Length;

   subtype Chunk_Offset is Natural range 0 .. Chunk_Length - 1;
   subtype Chunk_Number is Natural range 0 .. Chunk_Count - 1;

   type Slot_Chunk is array (Chunk_Offset) of Slot;
   type Slot_Chunk_Access is access Slot_Chunk;
   type Chunk_Table is array (Chunk_Number) of Slot_Chunk_Access;
   type Chunk_Table_Access is access Chunk_Table;

   --  Bytes charged for the chunk table and for each chunk.
   Table_Bytes : constant Byte_Count := 8 * Chunk_Count;
   Chunk_Bytes : constant Byte_Count := 32 * Chunk_Length;

   --  The handle of place Offset of chunk Chunk (one past the last handle for the very last
   --  place). Invariants are stated by chunk and place, so that no proof needs the division
   --  of Chunk_Of and Offset_Of except their link to this function.
   function Handle_At (Chunk : Chunk_Number; Offset : Chunk_Offset) return Object_Handle'Base
   is (Object_Handle'Base (Chunk) * Chunk_Length + Object_Handle'Base (Offset) + 1);

   --  Where the slot of a handle is: its chunk and its place in the chunk. Proofs know only
   --  the postcondition (the body is in the package body), so they never see the division.
   type Place is record
      Chunk  : Chunk_Number;
      Offset : Chunk_Offset;
   end record;

   function Place_Of (Handle : Valid_Handle) return Place
   with Post => Handle_At (Place_Of'Result.Chunk, Place_Of'Result.Offset) = Handle;

   --  The interned strings: an open-addressing set of string handles, probed linearly from
   --  their hash. It does not keep strings alive: the collector removes the strings it
   --  frees. A deleted entry keeps the probe sequences through it going.
   type Entry_State is (Empty_Entry, Used_Entry, Deleted_Entry);

   type Intern_Entry is record
      State  : Entry_State := Empty_Entry;
      Handle : Object_Handle := No_Object;
      Hash   : Unsigned_64 := 0;
   end record;

   Maximum_Intern_Capacity : constant := 2 ** 27;
   Minimum_Intern_Capacity : constant := 64;
   subtype Intern_Index is Natural range 0 .. Maximum_Intern_Capacity - 1;
   type Intern_Table is array (Intern_Index range <>) of Intern_Entry;
   type Intern_Table_Access is access Intern_Table;

   --  Bytes charged for each entry of the intern set.
   Entry_Bytes : constant Byte_Count := 24;

   type Heap is limited record
      Seed       : Pyro.Strings.Seed;
      Intern     : Intern_Table_Access := null;
      --  Used and deleted entries of the intern set: when to rebuild it. Only a trigger:
      --  nothing depends on its accuracy.
      Filled     : Natural := 0;
      Chunks     : Chunk_Table_Access := null;
      Slot_Count : Object_Handle := No_Object;
      --  The last freed slot, the start of the free list (checked when taken, so the list
      --  needs no invariant).
      Free_Head  : Object_Handle := No_Object;
      --  The last object made gray, the start of the gray list (checked when taken, so the
      --  list needs no invariant).
      Gray_Head  : Object_Handle := No_Object;
   end record;

   function Slot_Count (H : Heap) return Object_Handle
   is (H.Slot_Count);

   function Seed (H : Heap) return Pyro.Strings.Seed
   is (H.Seed);

   --  Chunk Chunk is allocated.
   function Has_Chunk (H : Heap; Chunk : Chunk_Number) return Boolean
   is (H.Chunks /= null and then H.Chunks (Chunk) /= null);

   function Kind_Of (H : Heap; Handle : Object_Handle) return Object_Kind
   is (if Handle in 1 .. Slot_Count (H) and then Has_Chunk (H, Place_Of (Handle).Chunk)
       then H.Chunks (Place_Of (Handle).Chunk) (Place_Of (Handle).Offset).Kind
       else Free_Object);

   function Color_Of (H : Heap; Handle : Object_Handle) return Object_Color
   is (if Handle in 1 .. Slot_Count (H) and then Has_Chunk (H, Place_Of (Handle).Chunk)
       then H.Chunks (Place_Of (Handle).Chunk) (Place_Of (Handle).Offset).Color
       else White);

   --  [proof] Every reference is canonical. Hidden, as a quantifier inside every slot's
   --  validity would weigh on every proof about slots; unfolded where a reference is read.
   function Refs_Canonical (Refs : Reference_Array) return Boolean
   is (for all Position in Refs'Range => Is_Canonical (Refs (Position)))
   with Ghost;
   pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Refs_Canonical);

   --  [proof] References are numbered from 1, at most Maximum_References, and canonical.
   function Refs_Valid (Refs : Reference_Array_Access) return Boolean
   is (Refs /= null
       and then Refs'First = 1
       and then Refs'Length <= Maximum_References
       and then Refs_Canonical (Refs.all))
   with Ghost;

   --  [proof] A slot holds what its kind says: a free slot owns nothing and is white, a
   --  string slot owns bytes 1 .. Length, at most Maximum_String_Length, a table slot a
   --  valid table and its metatable, and the others their references.
   function Slot_Valid (Item : Slot) return Boolean
   is (case Item.Kind is
         when Free_Object   =>
           Item.Bytes = null
           and then Item.Table = null
           and then Item.Refs = null
           and then Item.Color = White,
         when String_Object =>
           Item.Bytes /= null
           and then Item.Bytes'First = 1
           and then Item.Bytes'Last <= Maximum_String_Length
           and then Item.Table = null
           and then Item.Refs = null,
         when Table_Object  =>
           Item.Bytes = null
           and then Item.Table /= null
           and then Pyro.Tables.Is_Valid (Item.Table.all)
           and then Refs_Valid (Item.Refs)
           and then Item.Refs'Length = 1,
         when Closure_Object | Upvalue_Object | Host_Function_Object =>
           Item.Bytes = null and then Item.Table = null and then Refs_Valid (Item.Refs))
   with Ghost;
   --  Hidden, so that writing one slot leaves every other slot's validity as it was without
   --  the provers unfolding it; the body's slot-level procedures unfold it where needed.
   pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Slot_Valid);

   --  [proof] Slot Handle, of a heap with chunk table Chunks and Count slots, has its chunk
   --  and is valid when Handle is at most Count; otherwise it is free, white and owns nothing.
   --  Stated over the chunk table and the count rather than the heap, so that changing any
   --  other part of the heap keeps it as it is.
   function Place_Valid
     (Chunks : Chunk_Table_Access; Count : Object_Handle; Handle : Valid_Handle) return Boolean
   is (if Handle <= Count
       then Chunks /= null
            and then Chunks (Place_Of (Handle).Chunk) /= null
            and then Slot_Valid (Chunks (Place_Of (Handle).Chunk) (Place_Of (Handle).Offset))
       else Chunks = null
            or else Chunks (Place_Of (Handle).Chunk) = null
            or else (Chunks (Place_Of (Handle).Chunk) (Place_Of (Handle).Offset).Kind = Free_Object
                     and then Chunks (Place_Of (Handle).Chunk) (Place_Of (Handle).Offset).Bytes
                              = null
                     and then Chunks (Place_Of (Handle).Chunk) (Place_Of (Handle).Offset).Table
                              = null
                     and then Chunks (Place_Of (Handle).Chunk) (Place_Of (Handle).Offset).Refs
                              = null
                     and then Chunks (Place_Of (Handle).Chunk) (Place_Of (Handle).Offset).Color
                              = White))
   with Ghost;

   function Handle_Valid (H : Heap; Handle : Valid_Handle) return Boolean
   is (Place_Valid (H.Chunks, H.Slot_Count, Handle))
   with Ghost;

   --  [proof] S followed by the references Refs.
   function Append_All
     (S : Value_Sequences.Sequence; Refs : Reference_Array) return Value_Sequences.Sequence
   with
     Ghost,
     Global => null,
     Pre    =>
       Value_Sequences.Last (S) <= Pyro.Tables.Maximum_Entry_Count
       and then Refs'First = 1
       and then Refs'Length <= Maximum_References,
     Post   =>
       Value_Sequences.Last (Append_All'Result) = Value_Sequences.Last (S) + Refs'Length
       and then (for all Position in 1 .. Value_Sequences.Last (S) =>
                   Value_Sequences.Get (Append_All'Result, Position)
                   = Value_Sequences.Get (S, Position))
       and then (for all Position in 1 .. Refs'Length =>
                   Value_Sequences.Get (Append_All'Result, Value_Sequences.Last (S) + Position)
                   = Refs (Position));

   --  [proof] The values slot Item holds: a table's entries, then the slot's references.
   function Slot_Children (Item : Slot) return Value_Sequences.Sequence
   is (case Item.Kind is
         when Free_Object | String_Object => Value_Sequences.Empty_Sequence,
         when Table_Object =>
           (if Item.Table = null then Value_Sequences.Empty_Sequence
            elsif Item.Refs = null then Pyro.Tables.Entries (Item.Table.all)
            elsif Item.Refs'First = 1 and then Item.Refs'Length <= Maximum_References
            then Append_All (Pyro.Tables.Entries (Item.Table.all), Item.Refs.all)
            else Value_Sequences.Empty_Sequence),
         when Closure_Object | Upvalue_Object | Host_Function_Object =>
           (if Item.Refs /= null
               and then Item.Refs'First = 1
               and then Item.Refs'Length <= Maximum_References
            then Append_All (Value_Sequences.Empty_Sequence, Item.Refs.all)
            else Value_Sequences.Empty_Sequence))
   with Ghost;

   function Children (H : Heap; Handle : Valid_Handle) return Value_Sequences.Sequence
   is (if Kind_Of (H, Handle) = Free_Object then Value_Sequences.Empty_Sequence
       else Slot_Children (H.Chunks (Place_Of (Handle).Chunk) (Place_Of (Handle).Offset)));

   function Reference_Count (H : Heap; Handle : Valid_Handle) return Natural
   is (if Kind_Of (H, Handle) /= Free_Object
          and then H.Chunks (Place_Of (Handle).Chunk) (Place_Of (Handle).Offset).Refs /= null
          and then H.Chunks (Place_Of (Handle).Chunk) (Place_Of (Handle).Offset).Refs'First = 1
          and then H.Chunks (Place_Of (Handle).Chunk) (Place_Of (Handle).Offset).Refs'Length
                   <= Maximum_References
       then H.Chunks (Place_Of (Handle).Chunk) (Place_Of (Handle).Offset).Refs'Length
       else 0);

   function Reference_At (H : Heap; Handle : Valid_Handle; Position : Positive) return Value
   is (H.Chunks (Place_Of (Handle).Chunk) (Place_Of (Handle).Offset).Refs (Position));

   function Tag_Of (H : Heap; Handle : Valid_Handle) return Natural
   is (if Kind_Of (H, Handle) /= Free_Object
       then H.Chunks (Place_Of (Handle).Chunk) (Place_Of (Handle).Offset).Tag
       else 0);

   function Table_Model (H : Heap; T : Valid_Handle) return Value_Maps.Map
   is (if H.Chunks (Place_Of (T).Chunk) (Place_Of (T).Offset).Table /= null
       then Pyro.Tables.Model (H.Chunks (Place_Of (T).Chunk) (Place_Of (T).Offset).Table.all)
       else Value_Maps.Empty_Map);

   --  [proof] The intern set has the shape probing needs, and its used entries are strings.
   function Intern_Valid (H : Heap) return Boolean
   is (H.Intern = null
       or else (H.Intern'First = 0
                and then H.Intern'Length >= 1
                and then (for all Index in H.Intern'Range =>
                            (if H.Intern (Index).State = Used_Entry
                             then Kind_Of (H, H.Intern (Index).Handle) = String_Object))))
   with Ghost;

   --  [proof] Every value an object holds refers to an object. Hidden, so that only the
   --  operations that change objects see the ghost graph; they restore it through lemmas.
   function Refs_Live (H : Heap) return Boolean
   is (Graph_Live (Kinds (H), Graph (H)))
   with Ghost, Post => (if Slot_Count (H) = 0 then Refs_Live'Result);
   pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Refs_Live);

   function Is_Valid (H : Heap) return Boolean
   is ((Slot_Count (H) = 0 or else H.Chunks /= null)
       and then (for all Handle in Valid_Handle =>
                   Place_Valid (H.Chunks, H.Slot_Count, Handle))
       and then Intern_Valid (H)
       and then Refs_Live (H));

   function String_Length (H : Heap; S : Object_Handle) return Natural
   is (if Kind_Of (H, S) = String_Object
          and then H.Chunks (Place_Of (S).Chunk) (Place_Of (S).Offset).Bytes /= null
       then Natural (H.Chunks (Place_Of (S).Chunk) (Place_Of (S).Offset).Bytes'Length)
       else 0);

   function String_Byte (H : Heap; S : Object_Handle; Position : Byte_Position) return Character
   is (if Kind_Of (H, S) = String_Object
          and then H.Chunks (Place_Of (S).Chunk) (Place_Of (S).Offset).Bytes /= null
          and then Position in H.Chunks (Place_Of (S).Chunk) (Place_Of (S).Offset).Bytes'Range
       then H.Chunks (Place_Of (S).Chunk) (Place_Of (S).Offset).Bytes (Position)
       else ASCII.NUL);

   function String_Hash (H : Heap; S : Object_Handle) return Unsigned_64
   is (H.Chunks (Place_Of (S).Chunk) (Place_Of (S).Offset).Hash);

   function Is_Released (H : Heap) return Boolean
   is (H.Chunks = null and then H.Intern = null);

end Pyro.Heap;
