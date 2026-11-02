--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  The heap: numbered slots holding Lua's objects, reached by handles.

with Interfaces;          use Interfaces;
with Pyro.Kind_Sequences;
with Pyro.Memory_Budgets; use Pyro.Memory_Budgets;
with Pyro.Strings;
with Pyro.Values;         use Pyro.Values;

package Pyro.Heap with SPARK_Mode => On, Always_Terminates is

   use type Pyro.Strings.Seed;

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
   with Global => null, Post => (if Handle > Slot_Count (H) then Kind_Of'Result = Free_Object);

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

   --  [proof] Every slot is either free and empty or holds one object of its kind, and every
   --  handle stored in an object refers to an object.
   function Is_Valid (H : Heap) return Boolean
   with Ghost, Global => null;

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

   --  A slot: what it holds, and what it owns. A free slot links to the next free one; a
   --  string slot keeps its hash.
   type Slot is record
      Kind      : Object_Kind := Free_Object;
      Next_Free : Object_Handle := No_Object;
      Hash      : Unsigned_64 := 0;
      Bytes     : Byte_Array_Access := null;
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

   --  [proof] A slot holds what its kind says: a free slot owns nothing, a string slot owns
   --  bytes 1 .. Length, at most Maximum_String_Length.
   function Slot_Valid (Item : Slot) return Boolean
   is (case Item.Kind is
         when Free_Object   => Item.Bytes = null,
         when String_Object =>
           Item.Bytes /= null
           and then Item.Bytes'First = 1
           and then Item.Bytes'Last <= Maximum_String_Length,
         when Table_Object  => False)
   with Ghost;

   --  [proof] Slot Handle has its chunk and is valid when Handle is at most Slot_Count;
   --  otherwise it is free and owns nothing.
   function Handle_Valid (H : Heap; Handle : Valid_Handle) return Boolean
   is (if Handle <= Slot_Count (H)
       then Has_Chunk (H, Place_Of (Handle).Chunk)
            and then Slot_Valid (H.Chunks (Place_Of (Handle).Chunk) (Place_Of (Handle).Offset))
       else not Has_Chunk (H, Place_Of (Handle).Chunk)
            or else (H.Chunks (Place_Of (Handle).Chunk) (Place_Of (Handle).Offset).Kind
                     = Free_Object
                     and then H.Chunks (Place_Of (Handle).Chunk) (Place_Of (Handle).Offset).Bytes
                              = null))
   with Ghost;

   --  [proof] The intern set has the shape probing needs, and its used entries are strings.
   function Intern_Valid (H : Heap) return Boolean
   is (H.Intern = null
       or else (H.Intern'First = 0
                and then H.Intern'Length >= 1
                and then (for all Index in H.Intern'Range =>
                            (if H.Intern (Index).State = Used_Entry
                             then Kind_Of (H, H.Intern (Index).Handle) = String_Object))))
   with Ghost;

   function Is_Valid (H : Heap) return Boolean
   is ((Slot_Count (H) = 0 or else H.Chunks /= null)
       and then (for all Handle in Valid_Handle => Handle_Valid (H, Handle))
       and then Intern_Valid (H));

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
