--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  The heap: numbered slots holding Lua's objects, reached by handles.

with Ada.Unchecked_Deallocation;

package body Pyro.Heap with SPARK_Mode => On is

   procedure Free_Bytes is new Ada.Unchecked_Deallocation (Byte_Array, Byte_Array_Access);
   procedure Free_Chunk is new Ada.Unchecked_Deallocation (Slot_Chunk, Slot_Chunk_Access);
   procedure Free_Table is new Ada.Unchecked_Deallocation (Chunk_Table, Chunk_Table_Access);
   procedure Free_Intern is new Ada.Unchecked_Deallocation (Intern_Table, Intern_Table_Access);

   function Place_Of (Handle : Valid_Handle) return Place is
   begin
      return (Chunk  => Natural (Handle - 1) / Chunk_Length,
              Offset => Natural (Handle - 1) mod Chunk_Length);
   end Place_Of;

   --  The intern set is allocated.
   function Has_Intern (H : Heap) return Boolean
   is (H.Intern /= null);

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
       and then Has_Intern (H) = Has_Intern (H)'Old
       and then Seed (H) = Seed (H)'Old
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
           (others => (Kind => Free_Object, Next_Free => No_Object, Hash => 0, Bytes => null));
      end if;
      pragma Assert (Handle_Valid (H, Next));
      H.Slot_Count := Next;
      Handle := Next;
   end Take_Slot;

   procedure Set_Seed (H : in out Heap; Key : Pyro.Strings.Seed) is
   begin
      H.Seed := Key;
   end Set_Seed;

   --  The place where the probe for Hash starts, and its Step-th place, in a set of
   --  Capacity entries.
   function Probe (Hash : Unsigned_64; Step, Capacity : Positive) return Intern_Index
   is ((Natural (Hash and Unsigned_64 (Capacity - 1)) + (Step - 1)) mod Capacity)
   with
     Pre  => Capacity <= Maximum_Intern_Capacity and then Step <= Capacity,
     Post => Probe'Result < Capacity;

   --  String S holds exactly the bytes of Text.
   function Same_Bytes (H : Heap; S : Object_Handle; Text : Byte_Array) return Boolean
   with
     Global => null,
     Pre    => Is_Valid (H) and then Kind_Of (H, S) = String_Object,
     Post   =>
       (if Same_Bytes'Result
        then String_Length (H, S) = Text'Length
             and then (for all Position in 1 .. Text'Length =>
                         String_Byte (H, S, Byte_Position (Position))
                         = Text (Text'First - 1 + Byte_Position (Position))))
   is
      P : constant Place := Place_Of (S);
   begin
      pragma Assert (Handle_Valid (H, S));
      if H.Chunks (P.Chunk) (P.Offset).Bytes'Length /= Text'Length then
         return False;
      end if;
      for Position in 1 .. Text'Length loop
         if H.Chunks (P.Chunk) (P.Offset).Bytes (Byte_Position (Position))
           /= Text (Text'First - 1 + Byte_Position (Position))
         then
            return False;
         end if;
         pragma Loop_Invariant
           (for all Earlier in 1 .. Position =>
              H.Chunks (P.Chunk) (P.Offset).Bytes (Byte_Position (Earlier))
              = Text (Text'First - 1 + Byte_Position (Earlier)));
      end loop;
      return True;
   end Same_Bytes;

   --  The interned string holding the bytes of Text, whose hash is Hash, or No_Object.
   function Find_String (H : Heap; Text : Byte_Array; Hash : Unsigned_64) return Object_Handle
   with
     Global => null,
     Pre    => Is_Valid (H),
     Post   =>
       (if Find_String'Result /= No_Object
        then Kind_Of (H, Find_String'Result) = String_Object
             and then String_Length (H, Find_String'Result) = Text'Length
             and then (for all Position in 1 .. Text'Length =>
                         String_Byte (H, Find_String'Result, Byte_Position (Position))
                         = Text (Text'First - 1 + Byte_Position (Position))))
   is
      Index : Intern_Index;
   begin
      if H.Intern = null then
         return No_Object;
      end if;
      for Step in 1 .. H.Intern'Length loop
         Index := Probe (Hash, Step, H.Intern'Length);
         exit when H.Intern (Index).State = Empty_Entry;
         if H.Intern (Index).State = Used_Entry
           and then H.Intern (Index).Hash = Hash
           and then Same_Bytes (H, H.Intern (Index).Handle, Text)
         then
            return H.Intern (Index).Handle;
         end if;
      end loop;
      return No_Object;
   end Find_String;

   --  Puts string S, whose hash is Hash, in the first place of its probe sequence that is not
   --  used. Success is False when every place is used.
   procedure Insert
     (Table   : in out Intern_Table;
      S       : Object_Handle;
      Hash    : Unsigned_64;
      Success : out Boolean)
   with
     Global => null,
     Pre    => Table'First = 0 and then Table'Length >= 1,
     Post   =>
       (for all Index in Table'Range =>
          (if Table (Index).State = Used_Entry
           then (Table'Old (Index).State = Used_Entry and then Table (Index) = Table'Old (Index))
                or else Table (Index) = (State => Used_Entry, Handle => S, Hash => Hash)))
   is
      Index : Intern_Index;
   begin
      Success := False;
      for Step in 1 .. Table'Length loop
         Index := Probe (Hash, Step, Table'Length);
         if Table (Index).State /= Used_Entry then
            Table (Index) := (State => Used_Entry, Handle => S, Hash => Hash);
            Success := True;
            return;
         end if;
      end loop;
   end Insert;

   --  Makes room in the intern set for one more string: rebuilds it, twice as large as its
   --  used entries need, when its used and deleted entries would pass three quarters of it.
   --  Success is False when Budget cannot pay.
   procedure Make_Room (H : in out Heap; Budget : in out Memory_Budget; Success : out Boolean)
   with
     Global => null,
     Pre    => Is_Valid (H),
     Post   =>
       Is_Valid (H)
       and then Limit (Budget) = Limit (Budget)'Old
       and then Slot_Count (H) = Slot_Count (H)'Old
       and then Seed (H) = Seed (H)'Old
       and then (for all Handle in 1 .. Slot_Count (H) =>
                   Kind_Of (H, Handle) = Kind_Sequences.Get (Kinds (H)'Old, Handle))
       and then (if Success then Has_Intern (H))
   is
      Used     : Natural := 0;
      Capacity : Natural;
      Table    : Intern_Table_Access;
      Added    : Boolean;
   begin
      Success := True;
      if H.Intern /= null and then H.Filled < H.Intern'Length / 4 * 3 then
         return;
      end if;
      if H.Intern /= null then
         for Index in H.Intern'Range loop
            if H.Intern (Index).State = Used_Entry and then Used < Natural'Last then
               Used := Used + 1;
            end if;
         end loop;
      end if;
      Capacity := Minimum_Intern_Capacity;
      while Capacity <= Maximum_Intern_Capacity / 2 and then Capacity / 2 <= Used loop
         pragma Loop_Variant (Increases => Capacity);
         pragma Loop_Invariant (Capacity in Minimum_Intern_Capacity .. Maximum_Intern_Capacity);
         Capacity := Capacity * 2;
      end loop;
      Charge (Budget, Entry_Bytes * Byte_Count (Capacity), Success);
      if not Success then
         return;
      end if;
      Table := new Intern_Table'(0 .. Capacity - 1 => (State => Empty_Entry, Handle => No_Object,
                                                        Hash => 0));
      Used := 0;
      if H.Intern /= null then
         for Index in H.Intern'Range loop
            if H.Intern (Index).State = Used_Entry then
               Insert (Table.all, H.Intern (Index).Handle, H.Intern (Index).Hash, Added);
               if not Added then
                  --  Not reached: the new set has twice the room its used entries need.
                  Free_Intern (Table);
                  Release (Budget, Entry_Bytes * Byte_Count (Capacity));
                  Success := False;
                  return;
               end if;
               if Used < Natural'Last then
                  Used := Used + 1;
               end if;
            end if;
            pragma Loop_Invariant (Table /= null and then Table'First = 0);
            pragma Loop_Invariant (Table'Length = Capacity);
            pragma Loop_Invariant
              (for all Other in Table'Range =>
                 (if Table (Other).State = Used_Entry
                  then Kind_Of (H, Table (Other).Handle) = String_Object));
            pragma Loop_Invariant (Limit (Budget) = Limit (Budget)'Loop_Entry);
         end loop;
         Release (Budget, Entry_Bytes * Byte_Count (H.Intern'Length));
      end if;
      Free_Intern (H.Intern);
      H.Intern := Table;
      H.Filled := Used;
   end Make_Room;

   --  A new string slot holding Text, whose hash is Hash, entered in the intern set. Result
   --  is No_Object (and the heap keeps its objects) when Budget cannot pay or every handle is
   --  in use.
   procedure Add_String
     (H      : in out Heap;
      Budget : in out Memory_Budget;
      Text   : Byte_Array;
      Hash   : Unsigned_64;
      Result : out Object_Handle)
   with
     Global => null,
     Pre    => Is_Valid (H) and then Has_Intern (H) and then Text'First = 1
               and then Text'Length <= Maximum_String_Length,
     Post   =>
       Is_Valid (H)
       and then Limit (Budget) = Limit (Budget)'Old
       and then Seed (H) = Seed (H)'Old
       and then Keeps_Objects (Kinds (H)'Old, Kinds (H))
       and then (if Result /= No_Object
                 then Kind_Of (H, Result) = String_Object
                      and then String_Length (H, Result) = Text'Length
                      and then (for all Position in 1 .. Text'Length =>
                                  String_Byte (H, Result, Byte_Position (Position))
                                  = Text (Byte_Position (Position))))
   is
      Cost    : constant Byte_Count := Byte_Count (Text'Length) + Object_Overhead;
      Success : Boolean;
      P       : Place;
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
      P := Place_Of (Result);
      pragma Assert (Handle_Valid (H, Result));
      H.Chunks (P.Chunk) (P.Offset).Kind := String_Object;
      H.Chunks (P.Chunk) (P.Offset).Hash := Hash;
      H.Chunks (P.Chunk) (P.Offset).Bytes := new Byte_Array'(Text);
      Insert (H.Intern.all, Result, Hash, Success);
      if Success and then H.Filled < Natural'Last then
         H.Filled := H.Filled + 1;
      end if;
   end Add_String;

   procedure New_String
     (H      : in out Heap;
      Budget : in out Memory_Budget;
      Text   : Byte_Array;
      Result : out Object_Handle)
   is
      Hash    : constant Unsigned_64 := Pyro.Strings.Hash (H.Seed, Text);
      Copy    : constant Byte_Array (1 .. Text'Length) := Text;
      Success : Boolean;
   begin
      Result := Find_String (H, Text, Hash);
      if Result /= No_Object then
         return;
      end if;
      Make_Room (H, Budget, Success);
      if Success then
         Add_String (H, Budget, Copy, Hash, Result);
      end if;
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
      if H.Intern /= null then
         Release (Budget, Entry_Bytes * Byte_Count (H.Intern'Length));
      end if;
      Free_Intern (H.Intern);
      H.Filled := 0;
      H.Slot_Count := No_Object;
      H.Free_Head := No_Object;
   end Clear;

end Pyro.Heap;
