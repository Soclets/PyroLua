--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  The heap: numbered slots holding Lua's objects, reached by handles.

with Pyro.Kind_Sequences;
with Pyro.Memory_Budgets; use Pyro.Memory_Budgets;
with Pyro.Values;         use Pyro.Values;

package Pyro.Heap with SPARK_Mode => On, Always_Terminates is

   --  The longest string, in bytes.
   Maximum_String_Length : constant := 2 ** 30 - 1;

   --  The bytes of a string.
   type Byte_Array is array (Byte_Position range <>) of Character;

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

   --  A new string holding the bytes of Text, or No_Object (and the heap keeps its objects)
   --  when Budget cannot pay for it or every handle is in use.
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
       and then (if Result /= No_Object
                 then Kind_Of (H, Result) = String_Object
                      and then String_Length (H, Result) = Text'Length);

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

   --  A slot: what it holds, and what it owns. A free slot links to the next free one.
   type Slot is record
      Kind      : Object_Kind := Free_Object;
      Next_Free : Object_Handle := No_Object;
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

   type Heap is limited record
      Chunks     : Chunk_Table_Access := null;
      Slot_Count : Object_Handle := No_Object;
      --  The last freed slot, the start of the free list (checked when taken, so the list
      --  needs no invariant).
      Free_Head  : Object_Handle := No_Object;
   end record;

   function Slot_Count (H : Heap) return Object_Handle
   is (H.Slot_Count);

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

   function Is_Valid (H : Heap) return Boolean
   is ((Slot_Count (H) = 0 or else H.Chunks /= null)
       and then (for all Handle in Valid_Handle => Handle_Valid (H, Handle)));

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

   function Is_Released (H : Heap) return Boolean
   is (H.Chunks = null);

end Pyro.Heap;
