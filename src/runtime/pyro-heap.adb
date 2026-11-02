--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  The heap: numbered slots holding Lua's objects, reached by handles.

with Ada.Unchecked_Deallocation;

package body Pyro.Heap with SPARK_Mode => On is

   procedure Free_Bytes is new Ada.Unchecked_Deallocation (Byte_Array, Byte_Array_Access);
   procedure Free_Chunk is new Ada.Unchecked_Deallocation (Slot_Chunk, Slot_Chunk_Access);
   procedure Free_Table is new Ada.Unchecked_Deallocation (Chunk_Table, Chunk_Table_Access);

   function Place_Of (Handle : Valid_Handle) return Place is
   begin
      return (Chunk  => Natural (Handle - 1) / Chunk_Length,
              Offset => Natural (Handle - 1) mod Chunk_Length);
   end Place_Of;

   function Kinds (H : Heap) return Kind_Sequences.Sequence is
      Result : Kind_Sequences.Sequence;
   begin
      for Handle in 1 .. Slot_Count (H) loop
         Result := Kind_Sequences.Add (Result, Kind_Of (H, Handle));
         pragma Loop_Invariant (Kind_Sequences.Last (Result) = Handle);
         pragma Loop_Invariant
           (for all Earlier in 1 .. Handle =>
              Kind_Sequences.Get (Result, Earlier) = Kind_Of (H, Earlier));
      end loop;
      return Result;
   end Kinds;

   --  Takes a slot for a new object: the first on the free list, or a new one after the
   --  others. Handle is No_Object when Budget cannot pay or every handle is in use. The slot
   --  is still free and owns nothing.
   procedure Take_Slot (H : in out Heap; Budget : in out Memory_Budget; Handle : out Object_Handle)
   with
     Global => null,
     Pre    => Is_Valid (H),
     Post   =>
       Is_Valid (H)
       and then Limit (Budget) = Limit (Budget)'Old
       and then Slot_Count (H) >= Slot_Count (H)'Old
       and then (for all Other in 1 .. Slot_Count (H)'Old =>
                   Kind_Of (H, Other) = Kind_Sequences.Get (Kinds (H)'Old, Other))
       and then (for all Other in Slot_Count (H)'Old + 1 .. Slot_Count (H) =>
                   Kind_Of (H, Other) = Free_Object)
       and then (if Handle /= No_Object
                 then Handle <= Slot_Count (H) and then Kind_Of (H, Handle) = Free_Object)
   is
      Success : Boolean;
      Next    : Object_Handle;
   begin
      Handle := No_Object;
      --  The start of the free list, unless it was taken again since.
      if H.Free_Head in 1 .. Slot_Count (H) and then Kind_Of (H, H.Free_Head) = Free_Object then
         Handle := H.Free_Head;
         pragma Assert (Handle_Valid (H, Handle));
         H.Free_Head := H.Chunks (Place_Of (Handle).Chunk) (Place_Of (Handle).Offset).Next_Free;
         return;
      end if;
      H.Free_Head := No_Object;
      --  A new slot.
      if Slot_Count (H) = Valid_Handle'Last then
         return;
      end if;
      Next := Slot_Count (H) + 1;
      if H.Chunks = null then
         Charge (Budget, Table_Bytes, Success);
         if not Success then
            return;
         end if;
         H.Chunks := new Chunk_Table'(others => null);
      end if;
      if H.Chunks (Place_Of (Next).Chunk) = null then
         Charge (Budget, Chunk_Bytes, Success);
         if not Success then
            return;
         end if;
         H.Chunks (Place_Of (Next).Chunk) := new Slot_Chunk'
           (others => (Kind => Free_Object, Next_Free => No_Object, Bytes => null));
      end if;
      pragma Assert (Handle_Valid (H, Next));
      H.Slot_Count := Next;
      Handle := Next;
   end Take_Slot;

   procedure New_String
     (H      : in out Heap;
      Budget : in out Memory_Budget;
      Text   : Byte_Array;
      Result : out Object_Handle)
   is
      Cost    : constant Byte_Count := Byte_Count (Text'Length) + Object_Overhead;
      Copy    : constant Byte_Array (1 .. Text'Length) := Text;
      Success : Boolean;
   begin
      Result := No_Object;
      Charge (Budget, Cost, Success);
      if not Success then
         return;
      end if;
      Take_Slot (H, Budget, Result);
      if Result = No_Object then
         Release (Budget, Cost);
         return;
      end if;
      pragma Assert (Handle_Valid (H, Result));
      H.Chunks (Place_Of (Result).Chunk) (Place_Of (Result).Offset).Kind := String_Object;
      H.Chunks (Place_Of (Result).Chunk) (Place_Of (Result).Offset).Bytes := new Byte_Array'(Copy);
   end New_String;

   procedure Clear (H : in out Heap; Budget : in out Memory_Budget) is
   begin
      if H.Chunks /= null then
         for Chunk in Chunk_Number loop
            if H.Chunks (Chunk) /= null then
               for Offset in Chunk_Offset loop
                  if H.Chunks (Chunk) (Offset).Bytes /= null then
                     Release
                       (Budget,
                        Byte_Count (H.Chunks (Chunk) (Offset).Bytes'Length) + Object_Overhead);
                  end if;
                  Free_Bytes (H.Chunks (Chunk) (Offset).Bytes);
                  pragma Loop_Invariant (Limit (Budget) = Limit (Budget)'Loop_Entry);
                  pragma Loop_Invariant
                    (for all Earlier in 0 .. Offset => H.Chunks (Chunk) (Earlier).Bytes = null);
               end loop;
               Release (Budget, Chunk_Bytes);
            end if;
            Free_Chunk (H.Chunks (Chunk));
            pragma Loop_Invariant (Limit (Budget) = Limit (Budget)'Loop_Entry);
            pragma Loop_Invariant (for all Earlier in 0 .. Chunk => H.Chunks (Earlier) = null);
         end loop;
         Release (Budget, Table_Bytes);
      end if;
      Free_Table (H.Chunks);
      H.Slot_Count := No_Object;
      H.Free_Head := No_Object;
   end Clear;

end Pyro.Heap;
