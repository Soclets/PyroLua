--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  The heap: numbered slots holding Lua's objects, reached by handles.

with Ada.Unchecked_Deallocation;

package body Pyro.Heap with SPARK_Mode => On is

   procedure Free_Bytes is new Ada.Unchecked_Deallocation (Byte_Array, Byte_Array_Access);
   procedure Free_Chunk is new Ada.Unchecked_Deallocation (Slot_Chunk, Slot_Chunk_Access);
   procedure Free_Table is new Ada.Unchecked_Deallocation (Chunk_Table, Chunk_Table_Access);
   procedure Free_Intern is new Ada.Unchecked_Deallocation (Intern_Table, Intern_Table_Access);
   procedure Free_Table_Object is new Ada.Unchecked_Deallocation (Pyro.Tables.Table, Table_Access);
   procedure Free_Refs is new Ada.Unchecked_Deallocation (Reference_Array, Reference_Array_Access);

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

   function Colors (H : Heap) return Color_Sequences.Sequence is
      Result : Color_Sequences.Sequence;
   begin
      for Handle in 1 .. Slot_Count (H) loop
         Result := Color_Sequences.Add (Result, Color_Of (H, Handle));
         pragma Loop_Invariant (Color_Sequences.Last (Result) = Handle);
         pragma Loop_Invariant
           (for all Earlier in 1 .. Handle =>
              Color_Sequences.Get (Result, Earlier) = Color_Of (H, Earlier));
      end loop;
      return Result;
   end Colors;

   function Graph (H : Heap) return Graph_Sequences.Sequence is
      Result : Graph_Sequences.Sequence;
   begin
      for Handle in 1 .. Slot_Count (H) loop
         Result := Graph_Sequences.Add (Result, Children (H, Handle));
         pragma Loop_Invariant (Graph_Sequences.Last (Result) = Handle);
         pragma Loop_Invariant
           (for all Earlier in 1 .. Handle =>
              Graph_Sequences.Get (Result, Earlier) = Children (H, Earlier));
      end loop;
      return Result;
   end Graph;

   function Append_All
     (S : Value_Sequences.Sequence; Refs : Reference_Array) return Value_Sequences.Sequence
   is
      Result : Value_Sequences.Sequence := S;
   begin
      for Position in Refs'Range loop
         Result := Value_Sequences.Add (Result, Refs (Position));
         pragma Loop_Invariant
           (Value_Sequences.Last (Result) = Value_Sequences.Last (S) + Position);
         pragma Loop_Invariant
           (for all Earlier in 1 .. Value_Sequences.Last (S) =>
              Value_Sequences.Get (Result, Earlier) = Value_Sequences.Get (S, Earlier));
         pragma Loop_Invariant
           (for all Earlier in 1 .. Position =>
              Value_Sequences.Get (Result, Value_Sequences.Last (S) + Earlier) = Refs (Earlier));
      end loop;
      return Result;
   end Append_All;

   --  [proof] What a table's new entries hold, they still hold with the table's references
   --  after them.
   procedure Lemma_Append_From
     (E1, E2 : Value_Sequences.Sequence; Refs : Reference_Array; Key, Item : Value)
   with
     Ghost,
     Global => null,
     Pre    =>
       Value_Sequences.Last (E1) <= Pyro.Tables.Maximum_Entry_Count
       and then Value_Sequences.Last (E2) <= Pyro.Tables.Maximum_Entry_Count
       and then Refs'First = 1
       and then Refs'Length <= Maximum_References
       and then Pyro.Tables.Entries_From (E2, E1, Key, Item),
     Post   => Pyro.Tables.Entries_From (Append_All (E2, Refs), Append_All (E1, Refs), Key, Item)
   is
      A1 : constant Value_Sequences.Sequence := Append_All (E1, Refs);
      A2 : constant Value_Sequences.Sequence := Append_All (E2, Refs);
   begin
      for Position in 1 .. Value_Sequences.Last (A2) loop
         if Position > Value_Sequences.Last (E2) then
            --  One of the references, also after the old entries.
            pragma Assert
              (Value_Sequences.Get (A2, Position)
               = Value_Sequences.Get
                   (A1, Value_Sequences.Last (E1) + Position - Value_Sequences.Last (E2)));
         elsif Value_Sequences.Get (A2, Position).Kind = Object_Value
           and then Value_Sequences.Get (A2, Position) /= Key
           and then Value_Sequences.Get (A2, Position) /= Item
         then
            pragma Assert
              (for some Earlier in 1 .. Value_Sequences.Last (E1) =>
                 Value_Sequences.Get (E1, Earlier) = Value_Sequences.Get (A2, Position)
                 and then Value_Sequences.Get (A1, Earlier) = Value_Sequences.Get (A2, Position));
         end if;
         pragma Loop_Invariant
           (for all Earlier in 1 .. Position =>
              Value_Sequences.Get (A2, Earlier).Kind /= Object_Value
              or else Value_Sequences.Get (A2, Earlier) = Key
              or else Value_Sequences.Get (A2, Earlier) = Item
              or else Value_Sequences.Contains
                        (A1, 1, Value_Sequences.Last (A1), Value_Sequences.Get (A2, Earlier)));
      end loop;
   end Lemma_Append_From;

   procedure Lemma_Graph_Live (H : Heap) is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Refs_Live);
   begin
      null;
   end Lemma_Graph_Live;

   --  [proof] Folds Refs_Live back, after an operation that changed objects.
   procedure Lemma_Refs_Live (H : Heap)
   with
     Ghost,
     Global => null,
     Pre    => Graph_Live (Kinds (H), Graph (H)),
     Post   => Refs_Live (H)
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Refs_Live);
   begin
      null;
   end Lemma_Refs_Live;

   --  [proof] Graph_Live (K2, G2) follows from Graph_Live (K1, G1) when K2 keeps the objects
   --  of K1 and every object of G2 holds no object or what it holds in G1.
   procedure Lemma_Graph_Grows (K1, K2 : Kind_Sequences.Sequence; G1, G2 : Graph_Sequences.Sequence)
   with
     Ghost,
     Global => null,
     Pre    =>
       Graph_Live (K1, G1)
       and then Keeps_Objects (K1, K2)
       and then (for all Handle in 1 .. Graph_Sequences.Last (G2) =>
                   (for all Position in 1 .. Value_Sequences.Last (Graph_Sequences.Get (G2, Handle))
                      => Value_Sequences.Get (Graph_Sequences.Get (G2, Handle), Position).Kind
                         /= Object_Value)
                   or else (Handle <= Graph_Sequences.Last (G1)
                            and then Graph_Sequences.Get (G2, Handle)
                                     = Graph_Sequences.Get (G1, Handle))),
     Post   => Graph_Live (K2, G2)
   is
   begin
      null;
   end Lemma_Graph_Grows;

   --  [proof] Graph_Live (K, G2) follows from Graph_Live (K, G1) when G2 differs from G1 only in
   --  table T, which holds only what it held, Key and Item, which K shows.
   procedure Lemma_Graph_Set
     (K         : Kind_Sequences.Sequence;
      G1, G2    : Graph_Sequences.Sequence;
      T         : Valid_Handle;
      Key, Item : Value)
   with
     Ghost,
     Global => null,
     Pre    =>
       Graph_Live (K, G1)
       and then Live_In (K, Key)
       and then Live_In (K, Item)
       and then T <= Graph_Sequences.Last (G1)
       and then Graph_Sequences.Last (G2) = Graph_Sequences.Last (G1)
       and then (for all Handle in 1 .. Graph_Sequences.Last (G2) =>
                   (if Handle /= T
                    then Graph_Sequences.Get (G2, Handle) = Graph_Sequences.Get (G1, Handle)))
       and then Pyro.Tables.Entries_From
                  (Graph_Sequences.Get (G2, T), Graph_Sequences.Get (G1, T), Key, Item),
     Post   => Graph_Live (K, G2)
   is
      After  : constant Value_Sequences.Sequence := Graph_Sequences.Get (G2, T);
      Before : constant Value_Sequences.Sequence := Graph_Sequences.Get (G1, T);
   begin
      for Position in 1 .. Value_Sequences.Last (After) loop
         if Value_Sequences.Get (After, Position).Kind = Object_Value
           and then Value_Sequences.Get (After, Position) /= Key
           and then Value_Sequences.Get (After, Position) /= Item
         then
            pragma Assert
              (for some Earlier in 1 .. Value_Sequences.Last (Before) =>
                 Value_Sequences.Get (Before, Earlier) = Value_Sequences.Get (After, Position)
                 and then Live_In (K, Value_Sequences.Get (Before, Earlier)));
         end if;
         pragma Loop_Invariant
           (for all Earlier in 1 .. Position => Live_In (K, Value_Sequences.Get (After, Earlier)));
      end loop;
   end Lemma_Graph_Set;

   --  [proof] Graph_Live (K2, G2) follows from Graph_Live (K1, G1) when K2 and G2 are K1 and G1
   --  with the objects C shows white freed, and the others refer only to objects that C does
   --  not show white (Closed).
   procedure Lemma_Graph_Sweep
     (K1, K2 : Kind_Sequences.Sequence;
      G1, G2 : Graph_Sequences.Sequence;
      C      : Color_Sequences.Sequence)
   with
     Ghost,
     Global => null,
     Pre    =>
       Graph_Live (K1, G1)
       and then Closed (C, G1)
       and then Kind_Sequences.Last (K1) = Graph_Sequences.Last (G1)
       and then Color_Sequences.Last (C) = Graph_Sequences.Last (G1)
       and then Kind_Sequences.Last (K2) = Kind_Sequences.Last (K1)
       and then Graph_Sequences.Last (G2) = Graph_Sequences.Last (G1)
       and then (for all Handle in 1 .. Kind_Sequences.Last (K1) =>
                   Kind_Sequences.Get (K2, Handle)
                   = (if Color_Sequences.Get (C, Handle) = White then Free_Object
                      else Kind_Sequences.Get (K1, Handle)))
       and then (for all Handle in 1 .. Graph_Sequences.Last (G1) =>
                   (if Color_Sequences.Get (C, Handle) = White
                    then Value_Sequences.Last (Graph_Sequences.Get (G2, Handle)) = 0
                    else Graph_Sequences.Get (G2, Handle) = Graph_Sequences.Get (G1, Handle))),
     Post   => Graph_Live (K2, G2)
   is
   begin
      null;
   end Lemma_Graph_Sweep;

   ----------------------------------------------------------------------------------------
   --  Slots, one at a time: the only places where a slot's validity is unfolded
   ----------------------------------------------------------------------------------------

   --  [proof] What a valid slot holds, by kind.
   procedure Lemma_Slot_Facts (Item : Slot)
   with
     Ghost,
     Global => null,
     Pre    => Slot_Valid (Item),
     Post   =>
       (case Item.Kind is
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
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Slot_Valid);
   begin
      null;
   end Lemma_Slot_Facts;

   --  [proof] A slot holding what its kind says is valid: what Lemma_Slot_Facts gives, after
   --  writing fields that do not change it.
   procedure Lemma_Slot_From_Facts (Item : Slot)
   with
     Ghost,
     Global => null,
     Pre    =>
       (case Item.Kind is
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
            Item.Bytes = null and then Item.Table = null and then Refs_Valid (Item.Refs)),
     Post   => Slot_Valid (Item)
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Slot_Valid);
   begin
      null;
   end Lemma_Slot_From_Facts;

   --  [proof] A free, white slot that owns nothing is valid.
   procedure Lemma_Free_Slot (Item : Slot)
   with
     Ghost,
     Global => null,
     Pre    =>
       Item.Kind = Free_Object
       and then Item.Bytes = null
       and then Item.Table = null
       and then Item.Refs = null
       and then Item.Color = White,
     Post   => Slot_Valid (Item)
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Slot_Valid);
   begin
      null;
   end Lemma_Free_Slot;

   --  Makes free slot Item a string holding Text, whose hash is Hash.
   procedure Init_String (Item : in out Slot; Text : Byte_Array; Hash : Unsigned_64)
   with
     Global => null,
     Pre    =>
       Slot_Valid (Item)
       and then Item.Kind = Free_Object
       and then Text'First = 1
       and then Text'Length <= Maximum_String_Length,
     Post   =>
       Slot_Valid (Item)
       and then Item.Kind = String_Object
       and then Item.Color = Item.Color'Old
       and then Item.Hash = Hash
       and then Item.Bytes /= null
       and then Item.Bytes'First = 1
       and then Pyro.Strings."=" (Item.Bytes.all, Text)
       and then Value_Sequences.Last (Slot_Children (Item)) = 0
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Slot_Valid);
   begin
      Item.Kind := String_Object;
      Item.Hash := Hash;
      Item.Bytes := new Byte_Array'(Text);
   end Init_String;

   --  Makes free slot Item an empty table keyed by Key, with no metatable.
   procedure Init_Table (Item : in out Slot; Key : Pyro.Strings.Seed)
   with
     Global => null,
     Pre    => Slot_Valid (Item) and then Item.Kind = Free_Object,
     Post   =>
       Slot_Valid (Item)
       and then Item.Kind = Table_Object
       and then Item.Color = Item.Color'Old
       and then Item.Table /= null
       and then Value_Maps.Is_Empty (Pyro.Tables.Model (Item.Table.all))
       and then Item.Refs /= null
       and then Item.Refs'First = 1
       and then Item.Refs'Length = 1
       and then Item.Refs (1) = Nil
       and then (for all Position in 1 .. Value_Sequences.Last (Slot_Children (Item)) =>
                   Value_Sequences.Get (Slot_Children (Item), Position).Kind /= Object_Value)
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Slot_Valid);
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Refs_Canonical);
   begin
      Item.Kind := Table_Object;
      Item.Table := new Pyro.Tables.Table;
      Item.Refs := new Reference_Array'(1 => Nil);
      Pyro.Tables.Set_Seed (Item.Table.all, Key);
   end Init_Table;

   --  Makes free slot Item an object of kind Kind, with number Tag and References references,
   --  all nil.
   procedure Init_Object
     (Item : in out Slot; Kind : Object_Kind; Tag : Natural; References : Natural)
   with
     Global => null,
     Pre    =>
       Slot_Valid (Item)
       and then Item.Kind = Free_Object
       and then Kind in Closure_Object | Upvalue_Object | Host_Function_Object
       and then References <= Maximum_References,
     Post   =>
       Slot_Valid (Item)
       and then Item.Kind = Kind
       and then Item.Color = Item.Color'Old
       and then Item.Tag = Tag
       and then Item.Refs /= null
       and then Item.Refs'First = 1
       and then Item.Refs'Length = References
       and then (for all Position in 1 .. References => Item.Refs (Position) = Nil)
       and then (for all Position in 1 .. Value_Sequences.Last (Slot_Children (Item)) =>
                   Value_Sequences.Get (Slot_Children (Item), Position).Kind /= Object_Value)
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Slot_Valid);
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Refs_Canonical);
   begin
      Item.Kind := Kind;
      Item.Tag := Tag;
      Item.Refs := new Reference_Array'(1 .. References => Nil);
   end Init_Object;

   --  Frees the white object slot Item holds, releasing its memory from Budget, and links the
   --  free slot to Link.
   procedure Free_Slot (Item : in out Slot; Budget : in out Memory_Budget; Link : Object_Handle)
   with
     Global => null,
     Pre    => Slot_Valid (Item) and then Item.Color = White,
     Post   =>
       Slot_Valid (Item)
       and then Item.Kind = Free_Object
       and then Item.Color = White
       and then Limit (Budget) = Limit (Budget)'Old
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Slot_Valid);
   begin
      case Item.Kind is
         when Free_Object =>
            null;
         when String_Object =>
            Release (Budget, Byte_Count (Item.Bytes'Length) + Object_Overhead);
            Free_Bytes (Item.Bytes);
         when Table_Object =>
            Pyro.Tables.Clear (Item.Table.all, Budget);
            Free_Table_Object (Item.Table);
            Release (Budget, Object_Overhead);
         when Closure_Object | Upvalue_Object | Host_Function_Object =>
            Release (Budget, Object_Overhead);
      end case;
      if Item.Refs /= null then
         Release (Budget, Reference_Bytes * Byte_Count (Item.Refs'Length));
      end if;
      Free_Refs (Item.Refs);
      Item.Kind := Free_Object;
      Item.Hash := 0;
      Item.Tag := 0;
      Item.Link := Link;
   end Free_Slot;

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
       and then (for all Other in 1 .. Slot_Count (H)'Old =>
                   Children (H, Other) = Graph_Sequences.Get (Graph (H)'Old, Other))
       and then Has_Intern (H) = Has_Intern (H)'Old
       and then Seed (H) = Seed (H)'Old
       and then (if Handle /= No_Object
                 then Handle <= Slot_Count (H) and then Kind_Of (H, Handle) = Free_Object)
   is
      K0      : constant Kind_Sequences.Sequence := Kinds (H) with Ghost;
      G0      : constant Graph_Sequences.Sequence := Graph (H) with Ghost;
      Success : Boolean;
      Next    : Object_Handle;
   begin
      Lemma_Graph_Live (H);
      Handle := No_Object;
      --  The start of the free list, unless it was taken again since.
      if H.Free_Head in 1 .. Slot_Count (H) and then Kind_Of (H, H.Free_Head) = Free_Object then
         Handle := H.Free_Head;
         pragma Assert (Handle_Valid (H, Handle));
         H.Free_Head := H.Chunks (Place_Of (Handle).Chunk) (Place_Of (Handle).Offset).Link;
            Lemma_Graph_Grows (K0, Kinds (H), G0, Graph (H));
         Lemma_Refs_Live (H);
         return;
      end if;
      H.Free_Head := No_Object;
      --  A new slot.
      if Slot_Count (H) = Valid_Handle'Last then
            Lemma_Graph_Grows (K0, Kinds (H), G0, Graph (H));
         Lemma_Refs_Live (H);
         return;
      end if;
      Next := Slot_Count (H) + 1;
      if H.Chunks = null then
         Charge (Budget, Table_Bytes, Success);
         if not Success then
                  Lemma_Graph_Grows (K0, Kinds (H), G0, Graph (H));
            Lemma_Refs_Live (H);
            return;
         end if;
         H.Chunks := new Chunk_Table'(others => null);
      end if;
      if H.Chunks (Place_Of (Next).Chunk) = null then
         Charge (Budget, Chunk_Bytes, Success);
         if not Success then
                  Lemma_Graph_Grows (K0, Kinds (H), G0, Graph (H));
            Lemma_Refs_Live (H);
            return;
         end if;
         H.Chunks (Place_Of (Next).Chunk) := new Slot_Chunk'
           (others => (Kind  => Free_Object, Color => White, Link => No_Object, Hash => 0,
                       Tag   => 0, Bytes => null, Table => null, Refs => null));
      end if;
      pragma Assert (Handle_Valid (H, Next));
      Lemma_Free_Slot (H.Chunks (Place_Of (Next).Chunk) (Place_Of (Next).Offset));
      H.Slot_Count := Next;
      Handle := Next;
      Lemma_Graph_Grows (K0, Kinds (H), G0, Graph (H));
      Lemma_Refs_Live (H);
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
      Lemma_Slot_Facts (H.Chunks (P.Chunk) (P.Offset));
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
      K0       : constant Kind_Sequences.Sequence := Kinds (H) with Ghost;
      G0       : constant Graph_Sequences.Sequence := Graph (H) with Ghost;
      Used     : Natural := 0;
      Capacity : Natural;
      Table    : Intern_Table_Access;
      Added    : Boolean;
   begin
      Lemma_Graph_Live (H);
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
      Lemma_Graph_Grows (K0, Kinds (H), G0, Graph (H));
      Lemma_Refs_Live (H);
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
      K1      : Kind_Sequences.Sequence with Ghost;
      G1      : Graph_Sequences.Sequence with Ghost;
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
      K1 := Kinds (H);
      G1 := Graph (H);
      Lemma_Graph_Live (H);
      Init_String (H.Chunks (P.Chunk) (P.Offset), Text, Hash);
      Insert (H.Intern.all, Result, Hash, Success);
      if Success and then H.Filled < Natural'Last then
         H.Filled := H.Filled + 1;
      end if;
      Lemma_Graph_Grows (K1, Kinds (H), G1, Graph (H));
      Lemma_Refs_Live (H);
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

   procedure New_Table
     (H      : in out Heap;
      Budget : in out Memory_Budget;
      Result : out Object_Handle)
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Refs_Canonical);
      Key     : constant Pyro.Strings.Seed := H.Seed;
      K1      : Kind_Sequences.Sequence with Ghost;
      G1      : Graph_Sequences.Sequence with Ghost;
      Success : Boolean;
      P       : Place;
   begin
      Result := No_Object;
      Charge (Budget, Object_Overhead + Reference_Bytes, Success);
      if not Success then
         return;
      end if;
      Take_Slot (H, Budget, Result);
      if Result = No_Object then
         Release (Budget, Object_Overhead + Reference_Bytes);
         return;
      end if;
      P := Place_Of (Result);
      pragma Assert (Handle_Valid (H, Result));
      K1 := Kinds (H);
      G1 := Graph (H);
      Lemma_Graph_Live (H);
      Init_Table (H.Chunks (P.Chunk) (P.Offset), Key);
      Lemma_Graph_Grows (K1, Kinds (H), G1, Graph (H));
      Lemma_Refs_Live (H);
   end New_Table;

   function Table_Get (H : Heap; T : Valid_Handle; Key : Value) return Value is
      P      : constant Place := Place_Of (T);
      Result : Value;
   begin
      pragma Assert (Handle_Valid (H, T));
      Lemma_Slot_Facts (H.Chunks (P.Chunk) (P.Offset));
      Lemma_Graph_Live (H);
      Result := Pyro.Tables.Get (H.Chunks (P.Chunk) (P.Offset).Table.all, Key);
      if Result /= Nil then
         Pyro.Tables.Lemma_Model_In_Entries (H.Chunks (P.Chunk) (P.Offset).Table.all, Key_Of (Key));
         pragma Assert (Graph_Sequences.Get (Graph (H), T) = Children (H, T));
      end if;
      return Result;
   end Table_Get;

   --  [proof] The slots are well formed: Is_Valid without the intern set and the graph, which
   --  the operations that change objects restore at their end.
   function Slots_Valid (H : Heap) return Boolean
   is ((Slot_Count (H) = 0 or else H.Chunks /= null)
       and then (for all Handle in Valid_Handle =>
                   Place_Valid (H.Chunks, H.Slot_Count, Handle)))
   with Ghost;

   --  Pyro.Tables.Set on the table that slot Item owns.
   procedure Set_In_Slot
     (Item   : in out Slot;
      Budget : in out Memory_Budget;
      Key    : Value;
      Stored : Value;
      Status : out Pyro.Tables.Set_Status)
   with
     Global => null,
     Pre    =>
       Slot_Valid (Item)
       and then Item.Kind = Table_Object
       and then Is_Canonical (Key)
       and then Is_Canonical (Stored),
     Post   =>
       Slot_Valid (Item)
       and then Item.Kind = Table_Object
       and then Item.Color = Item.Color'Old
       and then Item.Table /= null
       and then Limit (Budget) = Limit (Budget)'Old
       and then Pyro.Tables.Entries_From
                  (Slot_Children (Item), Slot_Children (Item)'Old, Key_Of (Key), Stored)
       and then (case Status is
                   when Pyro.Tables.Done          =>
                     Key_Of (Key) /= Nil
                     and then Pyro.Tables.Stored
                                (Pyro.Tables.Model (Item.Table.all),
                                 Pyro.Tables.Model (Item.Table.all)'Old, Key_Of (Key), Stored),
                   when Pyro.Tables.Invalid_Key   =>
                     Key_Of (Key) = Nil
                     and then Pyro.Tables.Model (Item.Table.all)
                              = Pyro.Tables.Model (Item.Table.all)'Old,
                   when Pyro.Tables.Out_Of_Memory =>
                     Pyro.Tables.Model (Item.Table.all) = Pyro.Tables.Model (Item.Table.all)'Old)
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Slot_Valid);
      Before : constant Value_Sequences.Sequence := Pyro.Tables.Entries (Item.Table.all)
      with Ghost;
   begin
      Pyro.Tables.Set (Item.Table.all, Budget, Key, Stored, Status);
      Lemma_Append_From
        (Before, Pyro.Tables.Entries (Item.Table.all), Item.Refs.all, Key_Of (Key), Stored);
   end Set_In_Slot;

   --  Pyro.Tables.Set on table T: every other object holds what it held.
   procedure Set_Entry
     (H      : in out Heap;
      Budget : in out Memory_Budget;
      T      : Valid_Handle;
      Key    : Value;
      Item   : Value;
      Status : out Pyro.Tables.Set_Status)
   with
     Global => null,
     Pre    =>
       Slots_Valid (H)
       and then Intern_Valid (H)
       and then Kind_Of (H, T) = Table_Object
       and then Is_Canonical (Key)
       and then Is_Canonical (Item),
     Post   =>
       Slots_Valid (H)
       and then Intern_Valid (H)
       and then Seed (H) = Seed (H)'Old
       and then Slot_Count (H) = Slot_Count (H)'Old
       and then Limit (Budget) = Limit (Budget)'Old
       and then (for all Other in 1 .. Slot_Count (H) =>
                   Kind_Of (H, Other) = Kind_Sequences.Get (Kinds (H)'Old, Other))
       and then (for all Other in 1 .. Slot_Count (H) =>
                   (if Other /= T
                    then Children (H, Other) = Graph_Sequences.Get (Graph (H)'Old, Other)))
       and then Pyro.Tables.Entries_From
                  (Children (H, T), Graph_Sequences.Get (Graph (H)'Old, T), Key_Of (Key), Item)
       and then (case Status is
                   when Pyro.Tables.Done          =>
                     Key_Of (Key) /= Nil
                     and then Pyro.Tables.Stored
                                (Table_Model (H, T), Table_Model (H, T)'Old, Key_Of (Key), Item),
                   when Pyro.Tables.Invalid_Key   =>
                     Key_Of (Key) = Nil and then Table_Model (H, T) = Table_Model (H, T)'Old,
                   when Pyro.Tables.Out_Of_Memory =>
                     Table_Model (H, T) = Table_Model (H, T)'Old)
   is
      P : constant Place := Place_Of (T);
   begin
      pragma Assert (Handle_Valid (H, T));
      Lemma_Slot_Facts (H.Chunks (P.Chunk) (P.Offset));
      Set_In_Slot (H.Chunks (P.Chunk) (P.Offset), Budget, Key, Item, Status);
      Lemma_Slot_Facts (H.Chunks (P.Chunk) (P.Offset));
      --  Not needed at run time: written again so that the provers see one slot changed.
      H.Chunks (P.Chunk) (P.Offset).Kind := Table_Object;
      Lemma_Slot_From_Facts (H.Chunks (P.Chunk) (P.Offset));
   end Set_Entry;

   procedure Table_Set
     (H      : in out Heap;
      Budget : in out Memory_Budget;
      T      : Valid_Handle;
      Key    : Value;
      Item   : Value;
      Status : out Pyro.Tables.Set_Status)
   is
      K0 : constant Kind_Sequences.Sequence := Kinds (H) with Ghost;
      G0 : constant Graph_Sequences.Sequence := Graph (H) with Ghost;
   begin
      Lemma_Graph_Live (H);
      pragma Assert (Live_In (K0, Key_Of (Key)) and then Live_In (K0, Item));
      Set_Entry (H, Budget, T, Key, Item, Status);
      Lemma_Graph_Set (K0, G0, Graph (H), T, Key_Of (Key), Item);
      Lemma_Refs_Live (H);
   end Table_Set;

   --  The number of values slot Item holds (Slot_Children), with no ghost code.
   function Slot_Child_Count (Item : Slot) return Natural
   is (case Item.Kind is
         when Free_Object | String_Object => 0,
         when Table_Object =>
           (if Item.Table /= null
               and then (Item.Refs = null
                         or else (Item.Refs'First = 1
                                  and then Item.Refs'Length <= Maximum_References))
            then Pyro.Tables.Entry_Count (Item.Table.all)
                 + (if Item.Refs = null then 0 else Item.Refs'Length)
            else 0),
         when Closure_Object | Upvalue_Object | Host_Function_Object =>
           (if Item.Refs /= null
               and then Item.Refs'First = 1
               and then Item.Refs'Length <= Maximum_References
            then Item.Refs'Length
            else 0))
   with Post => Slot_Child_Count'Result = Value_Sequences.Last (Slot_Children (Item));

   function Child_Count (H : Heap; Handle : Valid_Handle) return Natural
   is (if Kind_Of (H, Handle) = Free_Object then 0
       else Slot_Child_Count (H.Chunks (Place_Of (Handle).Chunk) (Place_Of (Handle).Offset)));

   function Child_At (H : Heap; Handle : Valid_Handle; Position : Positive) return Value is
      P       : constant Place := Place_Of (Handle);
      Entries : Natural := 0;
   begin
      Lemma_Graph_Live (H);
      pragma Assert (Graph_Sequences.Get (Graph (H), Handle) = Children (H, Handle));
      pragma Assert (Handle_Valid (H, Handle));
      Lemma_Slot_Facts (H.Chunks (P.Chunk) (P.Offset));
      if H.Chunks (P.Chunk) (P.Offset).Kind = Table_Object then
         Entries := Pyro.Tables.Entry_Count (H.Chunks (P.Chunk) (P.Offset).Table.all);
         if Position <= Entries then
            return Pyro.Tables.Entry_At (H.Chunks (P.Chunk) (P.Offset).Table.all, Position);
         end if;
      end if;
      return H.Chunks (P.Chunk) (P.Offset).Refs (Position - Entries);
   end Child_At;

   procedure Lemma_Reference_Live (H : Heap; Handle : Valid_Handle; Position : Positive) is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Refs_Canonical);
   begin
      Lemma_Graph_Live (H);
      pragma Assert (Handle_Valid (H, Handle));
      Lemma_Slot_Facts (H.Chunks (Place_Of (Handle).Chunk) (Place_Of (Handle).Offset));
      pragma Assert (Graph_Sequences.Get (Graph (H), Handle) = Children (H, Handle));
      pragma Assert
        (Reference_At (H, Handle, Position)
         = Value_Sequences.Get (Children (H, Handle), Child_Count (H, Handle)
                                - Reference_Count (H, Handle) + Position));
   end Lemma_Reference_Live;

   --  [proof] A sequence whose values are those of Before, or Stored, holds no object Before
   --  did not hold besides Stored.
   procedure Lemma_Replaced (Before, After : Value_Sequences.Sequence; Stored : Value)
   with
     Ghost,
     Global => null,
     Pre    =>
       Value_Sequences.Last (After) = Value_Sequences.Last (Before)
       and then (for all Index in 1 .. Value_Sequences.Last (After) =>
                   Value_Sequences.Get (After, Index) = Stored
                   or else Value_Sequences.Get (After, Index)
                           = Value_Sequences.Get (Before, Index)),
     Post   => Pyro.Tables.Entries_From (After, Before, Nil, Stored)
   is
   begin
      for Index in 1 .. Value_Sequences.Last (After) loop
         pragma Loop_Invariant
           (for all Earlier in 1 .. Index =>
              Value_Sequences.Get (After, Earlier).Kind /= Object_Value
              or else Value_Sequences.Get (After, Earlier) = Stored
              or else Value_Sequences.Contains
                        (Before, 1, Value_Sequences.Last (Before),
                         Value_Sequences.Get (After, Earlier)));
      end loop;
   end Lemma_Replaced;

   --  Makes reference Position of slot Item Stored.
   procedure Set_Reference_In_Slot (Item : in out Slot; Position : Positive; Stored : Value)
   with
     Global => null,
     Pre    =>
       Slot_Valid (Item)
       and then Item.Kind /= Free_Object
       and then Item.Refs /= null
       and then Position <= Item.Refs'Last
       and then Is_Canonical (Stored),
     Post   =>
       Slot_Valid (Item)
       and then Item.Kind = Item.Kind'Old
       and then Item.Color = Item.Color'Old
       and then Item.Tag = Item.Tag'Old
       and then Item.Refs /= null
       and then Item.Refs'First = 1
       and then Item.Refs'Last = Item.Refs'Last'Old
       and then Item.Refs (Position) = Stored
       and then Pyro.Tables.Entries_From
                  (Slot_Children (Item), Slot_Children (Item)'Old, Nil, Stored)
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Slot_Valid);
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Refs_Canonical);
      Before : constant Value_Sequences.Sequence := Slot_Children (Item) with Ghost;
   begin
      Item.Refs (Position) := Stored;
      pragma Assert (Value_Sequences.Last (Slot_Children (Item)) = Value_Sequences.Last (Before));
      pragma Assert
        (for all Index in 1 .. Value_Sequences.Last (Slot_Children (Item)) =>
           Value_Sequences.Get (Slot_Children (Item), Index) = Stored
           or else Value_Sequences.Get (Slot_Children (Item), Index)
                   = Value_Sequences.Get (Before, Index));
      Lemma_Replaced (Before, Slot_Children (Item), Stored);
   end Set_Reference_In_Slot;

   --  Set_Reference_In_Slot on object Handle: every other object holds what it held.
   procedure Set_Reference_Entry
     (H : in out Heap; Handle : Valid_Handle; Position : Positive; Item : Value)
   with
     Global => null,
     Pre    =>
       Slots_Valid (H)
       and then Intern_Valid (H)
       and then Kind_Of (H, Handle) /= Free_Object
       and then Position <= Reference_Count (H, Handle)
       and then Is_Canonical (Item),
     Post   =>
       Slots_Valid (H)
       and then Intern_Valid (H)
       and then Seed (H) = Seed (H)'Old
       and then Slot_Count (H) = Slot_Count (H)'Old
       and then (for all Other in 1 .. Slot_Count (H) =>
                   Kind_Of (H, Other) = Kind_Sequences.Get (Kinds (H)'Old, Other))
       and then (for all Other in 1 .. Slot_Count (H) =>
                   (if Other /= Handle
                    then Children (H, Other) = Graph_Sequences.Get (Graph (H)'Old, Other)))
       and then Pyro.Tables.Entries_From
                  (Children (H, Handle), Graph_Sequences.Get (Graph (H)'Old, Handle), Nil, Item)
       and then Reference_Count (H, Handle) = Reference_Count (H, Handle)'Old
       and then Tag_Of (H, Handle) = Tag_Of (H, Handle)'Old
       and then Reference_At (H, Handle, Position) = Item
   is
      P    : constant Place := Place_Of (Handle);
      Kind : constant Object_Kind := Kind_Of (H, Handle);
   begin
      pragma Assert (Handle_Valid (H, Handle));
      Lemma_Slot_Facts (H.Chunks (P.Chunk) (P.Offset));
      Set_Reference_In_Slot (H.Chunks (P.Chunk) (P.Offset), Position, Item);
      Lemma_Slot_Facts (H.Chunks (P.Chunk) (P.Offset));
      --  Not needed at run time: written again so that the provers see one slot changed.
      H.Chunks (P.Chunk) (P.Offset).Kind := Kind;
      Lemma_Slot_From_Facts (H.Chunks (P.Chunk) (P.Offset));
   end Set_Reference_Entry;

   procedure Set_Reference
     (H : in out Heap; Handle : Valid_Handle; Position : Positive; Item : Value)
   is
      K0 : constant Kind_Sequences.Sequence := Kinds (H) with Ghost;
      G0 : constant Graph_Sequences.Sequence := Graph (H) with Ghost;
   begin
      Lemma_Graph_Live (H);
      pragma Assert (Live_In (K0, Item));
      Set_Reference_Entry (H, Handle, Position, Item);
      Lemma_Graph_Set (K0, G0, Graph (H), Handle, Nil, Item);
      Lemma_Refs_Live (H);
   end Set_Reference;

   procedure New_Object
     (H          : in out Heap;
      Budget     : in out Memory_Budget;
      Kind       : Object_Kind;
      Tag        : Natural;
      References : Natural;
      Result     : out Object_Handle)
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Refs_Canonical);
      Cost    : constant Byte_Count := Object_Overhead + Reference_Bytes * Byte_Count (References);
      K1      : Kind_Sequences.Sequence with Ghost;
      G1      : Graph_Sequences.Sequence with Ghost;
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
      K1 := Kinds (H);
      G1 := Graph (H);
      Lemma_Graph_Live (H);
      Init_Object (H.Chunks (P.Chunk) (P.Offset), Kind, Tag, References);
      Lemma_Graph_Grows (K1, Kinds (H), G1, Graph (H));
      Lemma_Refs_Live (H);
   end New_Object;

   --  [proof] Only colours and links changed: every slot holds what K and G show.
   procedure Lemma_Same_Objects
     (H : Heap; K : Kind_Sequences.Sequence; G : Graph_Sequences.Sequence)
   with
     Ghost,
     Global => null,
     Pre    =>
       Kind_Sequences.Last (K) = Slot_Count (H)
       and then Graph_Sequences.Last (G) = Slot_Count (H)
       and then (for all Handle in 1 .. Slot_Count (H) =>
                   Kind_Of (H, Handle) = Kind_Sequences.Get (K, Handle)
                   and then Children (H, Handle) = Graph_Sequences.Get (G, Handle)),
     Post   => Kinds (H) = K and then Graph (H) = G
   is
   begin
      null;
   end Lemma_Same_Objects;

   --  Sets the colour of object Handle (a free slot stays white).
   procedure Set_Color (H : in out Heap; Handle : Valid_Handle; Color : Object_Color)
   with
     Global => null,
     Pre    =>
       Is_Valid (H)
       and then Handle <= Slot_Count (H)
       and then (Kind_Of (H, Handle) /= Free_Object or else Color = White),
     Post   =>
       Is_Valid (H)
       and then Slot_Count (H) = Slot_Count (H)'Old
       and then Kinds (H) = Kinds (H)'Old
       and then Graph (H) = Graph (H)'Old
       and then Color_Of (H, Handle) = Color
       and then (for all Other in 1 .. Slot_Count (H) =>
                   (if Other /= Handle
                    then Color_Of (H, Other) = Color_Sequences.Get (Colors (H)'Old, Other)))
   is
      P  : constant Place := Place_Of (Handle);
      K0 : constant Kind_Sequences.Sequence := Kinds (H) with Ghost;
      G0 : constant Graph_Sequences.Sequence := Graph (H) with Ghost;
      C0 : constant Color_Sequences.Sequence := Colors (H) with Ghost;
   begin
      Lemma_Graph_Live (H);
      pragma Assert (Handle_Valid (H, Handle));
      Lemma_Slot_Facts (H.Chunks (P.Chunk) (P.Offset));
      H.Chunks (P.Chunk) (P.Offset).Color := Color;
      Lemma_Slot_From_Facts (H.Chunks (P.Chunk) (P.Offset));
      pragma Assert (Place_Valid (H.Chunks, H.Slot_Count, Handle));
      pragma Assert
        (for all Other in Valid_Handle =>
           (if Other /= Handle then Place_Valid (H.Chunks, H.Slot_Count, Other)));
      Lemma_Same_Objects (H, K0, G0);
      Lemma_Refs_Live (H);
      pragma Assert
        (for all Other in 1 .. Slot_Count (H) =>
           (if Other /= Handle then Color_Of (H, Other) = Color_Sequences.Get (C0, Other)));
   end Set_Color;

   --  Sets the link of object Handle: the next object of the gray list.
   procedure Set_Link (H : in out Heap; Handle : Valid_Handle; Link : Object_Handle)
   with
     Global => null,
     Pre    =>
       Is_Valid (H)
       and then Handle <= Slot_Count (H)
       and then Kind_Of (H, Handle) /= Free_Object,
     Post   =>
       Is_Valid (H)
       and then Slot_Count (H) = Slot_Count (H)'Old
       and then Kinds (H) = Kinds (H)'Old
       and then Graph (H) = Graph (H)'Old
       and then Colors (H) = Colors (H)'Old
   is
      P  : constant Place := Place_Of (Handle);
      K0 : constant Kind_Sequences.Sequence := Kinds (H) with Ghost;
      G0 : constant Graph_Sequences.Sequence := Graph (H) with Ghost;
      C0 : constant Color_Sequences.Sequence := Colors (H) with Ghost;
   begin
      Lemma_Graph_Live (H);
      pragma Assert (Handle_Valid (H, Handle));
      Lemma_Slot_Facts (H.Chunks (P.Chunk) (P.Offset));
      H.Chunks (P.Chunk) (P.Offset).Link := Link;
      Lemma_Slot_From_Facts (H.Chunks (P.Chunk) (P.Offset));
      Lemma_Same_Objects (H, K0, G0);
      Lemma_Refs_Live (H);
      pragma Assert
        (for all Other in 1 .. Slot_Count (H) =>
           Color_Of (H, Other) = Color_Sequences.Get (C0, Other));
   end Set_Link;

   procedure Set_Tag (H : in out Heap; Handle : Valid_Handle; Tag : Natural) is
      P  : constant Place := Place_Of (Handle);
      K0 : constant Kind_Sequences.Sequence := Kinds (H) with Ghost;
      G0 : constant Graph_Sequences.Sequence := Graph (H) with Ghost;
   begin
      Lemma_Graph_Live (H);
      pragma Assert (Handle_Valid (H, Handle));
      Lemma_Slot_Facts (H.Chunks (P.Chunk) (P.Offset));
      H.Chunks (P.Chunk) (P.Offset).Tag := Tag;
      Lemma_Slot_From_Facts (H.Chunks (P.Chunk) (P.Offset));
      Lemma_Same_Objects (H, K0, G0);
      Lemma_Refs_Live (H);
   end Set_Tag;

   procedure Shade (H : in out Heap; Handle : Valid_Handle) is
      K0 : constant Kind_Sequences.Sequence := Kinds (H) with Ghost;
      G0 : constant Graph_Sequences.Sequence := Graph (H) with Ghost;
      C0 : constant Color_Sequences.Sequence := Colors (H) with Ghost;
   begin
      if Color_Of (H, Handle) /= White then
         return;
      end if;
      Set_Color (H, Handle, Gray);
      Set_Link (H, Handle, H.Gray_Head);
      Lemma_Graph_Live (H);
      H.Gray_Head := Handle;
      Lemma_Same_Objects (H, K0, G0);
      Lemma_Refs_Live (H);
      pragma Assert
        (for all Other in 1 .. Slot_Count (H) =>
           (if Other /= Handle then Color_Of (H, Other) = Color_Sequences.Get (C0, Other)));
   end Shade;

   procedure Take_Gray (H : in out Heap; Handle : out Object_Handle) is
      K0 : constant Kind_Sequences.Sequence := Kinds (H) with Ghost;
      G0 : constant Graph_Sequences.Sequence := Graph (H) with Ghost;
      C0 : constant Color_Sequences.Sequence := Colors (H) with Ghost;
      Head : constant Object_Handle := H.Gray_Head;
   begin
      Lemma_Graph_Live (H);
      Handle := No_Object;
      H.Gray_Head := No_Object;
      if Head in 1 .. Slot_Count (H)
        and then Kind_Of (H, Head) /= Free_Object
        and then Color_Of (H, Head) = Gray
      then
         Handle := Head;
         H.Gray_Head := H.Chunks (Place_Of (Head).Chunk) (Place_Of (Head).Offset).Link;
      end if;
      Lemma_Same_Objects (H, K0, G0);
      Lemma_Refs_Live (H);
      pragma Assert (Colors (H) = C0);
   end Take_Gray;

   procedure Blacken (H : in out Heap; Handle : Valid_Handle) is
   begin
      Set_Color (H, Handle, Black);
   end Blacken;

   procedure Whiten (H : in out Heap) is
      K0 : constant Kind_Sequences.Sequence := Kinds (H) with Ghost;
      G0 : constant Graph_Sequences.Sequence := Graph (H) with Ghost;
   begin
      for Handle in 1 .. Slot_Count (H) loop
         Set_Color (H, Handle, White);
         pragma Loop_Invariant (Is_Valid (H));
         pragma Loop_Invariant (Slot_Count (H) = Slot_Count (H)'Loop_Entry);
         pragma Loop_Invariant (Kinds (H) = K0 and then Graph (H) = G0);
         pragma Loop_Invariant (for all Earlier in 1 .. Handle => Color_Of (H, Earlier) = White);
      end loop;
      Lemma_Graph_Live (H);
      H.Gray_Head := No_Object;
      Lemma_Same_Objects (H, K0, G0);
      Lemma_Refs_Live (H);
      pragma Assert (for all Handle in 1 .. Slot_Count (H) => Color_Of (H, Handle) = White);
   end Whiten;

   --  Frees object Handle when it is white, and makes it white otherwise.
   procedure Sweep_Slot (H : in out Heap; Budget : in out Memory_Budget; Handle : Valid_Handle)
   with
     Global => null,
     Pre    => Slots_Valid (H) and then Handle <= Slot_Count (H) and then H.Intern = null,
     Post   =>
       Slots_Valid (H)
       and then H.Intern = null
       and then Seed (H) = Seed (H)'Old
       and then Slot_Count (H) = Slot_Count (H)'Old
       and then Limit (Budget) = Limit (Budget)'Old
       and then Color_Of (H, Handle) = White
       and then Kind_Of (H, Handle)
                = (if Color_Sequences.Get (Colors (H)'Old, Handle) = White then Free_Object
                   else Kind_Sequences.Get (Kinds (H)'Old, Handle))
       and then (if Color_Sequences.Get (Colors (H)'Old, Handle) = White
                 then Value_Sequences.Last (Children (H, Handle)) = 0
                 else Children (H, Handle) = Graph_Sequences.Get (Graph (H)'Old, Handle))
       and then (for all Other in 1 .. Slot_Count (H) =>
                   (if Other /= Handle
                    then Kind_Of (H, Other) = Kind_Sequences.Get (Kinds (H)'Old, Other)
                         and then Color_Of (H, Other)
                                  = Color_Sequences.Get (Colors (H)'Old, Other)
                         and then Children (H, Other)
                                  = Graph_Sequences.Get (Graph (H)'Old, Other)))
   is
      P         : constant Place := Place_Of (Handle);
      Free_Head : constant Object_Handle := H.Free_Head;
   begin
      pragma Assert (Handle_Valid (H, Handle));
      Lemma_Slot_Facts (H.Chunks (P.Chunk) (P.Offset));
      if H.Chunks (P.Chunk) (P.Offset).Kind = Free_Object then
         return;
      end if;
      if H.Chunks (P.Chunk) (P.Offset).Color /= White then
         H.Chunks (P.Chunk) (P.Offset).Color := White;
         Lemma_Slot_From_Facts (H.Chunks (P.Chunk) (P.Offset));
         pragma Assert (Color_Of (H, Handle) = White);
         return;
      end if;
      Free_Slot (H.Chunks (P.Chunk) (P.Offset), Budget, Free_Head);
      Lemma_Slot_Facts (H.Chunks (P.Chunk) (P.Offset));
      --  Not needed at run time: written again so that the provers see one slot changed.
      H.Chunks (P.Chunk) (P.Offset).Kind := Free_Object;
      Lemma_Slot_From_Facts (H.Chunks (P.Chunk) (P.Offset));
      pragma Assert (H.Chunks (P.Chunk) (P.Offset).Color = White);
      pragma Assert (Color_Of (H, Handle) = White);
      H.Free_Head := Handle;
   end Sweep_Slot;

   procedure Sweep (H : in out Heap; Budget : in out Memory_Budget) is
      K0 : constant Kind_Sequences.Sequence := Kinds (H) with Ghost;
      G0 : constant Graph_Sequences.Sequence := Graph (H) with Ghost;
      C0 : constant Color_Sequences.Sequence := Colors (H) with Ghost;
      --  The intern set, out of the heap while the slots change.
      Strings : Intern_Table_Access;
   begin
      Lemma_Graph_Live (H);
      Strings := H.Intern;
      H.Intern := null;
      H.Gray_Head := No_Object;
      --  The intern set does not keep strings alive: take out the ones about to be freed.
      if Strings /= null then
         for Index in Strings'Range loop
            if Strings (Index).State = Used_Entry
              and then Color_Of (H, Strings (Index).Handle) = White
            then
               Strings (Index).State := Deleted_Entry;
            end if;
            pragma Loop_Invariant
              (for all Other in Strings'Range =>
                 (if Strings (Other).State = Used_Entry
                  then Kind_Of (H, Strings (Other).Handle) = String_Object
                       and then (Other > Index
                                 or else Color_Of (H, Strings (Other).Handle) /= White)));
         end loop;
      end if;
      pragma Assert
        (Strings = null
         or else (for all Index in Strings'Range =>
                    (if Strings (Index).State = Used_Entry
                     then Strings (Index).Handle in 1 .. Slot_Count (H)
                          and then Kind_Sequences.Get (K0, Strings (Index).Handle)
                                   = String_Object
                          and then Color_Sequences.Get (C0, Strings (Index).Handle) /= White)));

      for Handle in 1 .. Slot_Count (H) loop
         Sweep_Slot (H, Budget, Handle);
         pragma Loop_Invariant (Slots_Valid (H) and then H.Intern = null);
         pragma Loop_Invariant (Seed (H) = Seed (H)'Loop_Entry);
         pragma Loop_Invariant (Slot_Count (H) = Slot_Count (H)'Loop_Entry);
         pragma Loop_Invariant (Limit (Budget) = Limit (Budget)'Loop_Entry);
         pragma Loop_Invariant
           (for all Other in 1 .. Slot_Count (H) =>
              Kind_Of (H, Other)
              = (if Other <= Handle and then Color_Sequences.Get (C0, Other) = White
                 then Free_Object
                 else Kind_Sequences.Get (K0, Other)));
         pragma Loop_Invariant
           (for all Other in 1 .. Slot_Count (H) =>
              (if Other <= Handle and then Color_Sequences.Get (C0, Other) = White
               then Value_Sequences.Last (Children (H, Other)) = 0
               else Children (H, Other) = Graph_Sequences.Get (G0, Other)));
         pragma Loop_Invariant
           (for all Other in 1 .. Slot_Count (H) =>
              Color_Of (H, Other)
              = (if Other <= Handle then White else Color_Sequences.Get (C0, Other)));
      end loop;
      H.Intern := Strings;
      Lemma_Graph_Sweep (K0, Kinds (H), G0, Graph (H), C0);
      Lemma_Refs_Live (H);
   end Sweep;

   --  Frees what slot Item owns, and releases it from Budget.
   procedure Release_Slot (Item : in out Slot; Budget : in out Memory_Budget)
   with
     Global => null,
     Post   =>
       Item.Bytes = null
       and then Item.Table = null
       and then Item.Refs = null
       and then Limit (Budget) = Limit (Budget)'Old
   is
   begin
      if Item.Bytes /= null then
         Release (Budget, Byte_Count (Item.Bytes'Length) + Object_Overhead);
      end if;
      Free_Bytes (Item.Bytes);
      if Item.Table /= null then
         Pyro.Tables.Clear (Item.Table.all, Budget);
         Release (Budget, Object_Overhead);
      end if;
      Free_Table_Object (Item.Table);
      if Item.Refs /= null then
         Release
           (Budget,
            Reference_Bytes * Byte_Count (Natural'Min (Item.Refs'Length, Maximum_References))
            + (if Item.Kind in Closure_Object | Upvalue_Object | Host_Function_Object
               then Object_Overhead else 0));
      end if;
      Free_Refs (Item.Refs);
   end Release_Slot;

   --  Frees chunk Chunk and what its slots own, and releases it all from Budget.
   procedure Release_Chunk (Chunk : in out Slot_Chunk_Access; Budget : in out Memory_Budget)
   with
     Global => null,
     Post   => Chunk = null and then Limit (Budget) = Limit (Budget)'Old
   is
   begin
      if Chunk = null then
         return;
      end if;
      for Offset in Chunk_Offset loop
         Release_Slot (Chunk (Offset), Budget);
         pragma Loop_Invariant (Limit (Budget) = Limit (Budget)'Loop_Entry);
         pragma Loop_Invariant
           (for all Earlier in 0 .. Offset =>
              Chunk (Earlier).Bytes = null
              and then Chunk (Earlier).Table = null
              and then Chunk (Earlier).Refs = null);
      end loop;
      Release (Budget, Chunk_Bytes);
      Free_Chunk (Chunk);
   end Release_Chunk;

   procedure Clear (H : in out Heap; Budget : in out Memory_Budget) is
   begin
      if H.Chunks /= null then
         for Chunk in Chunk_Number loop
            Release_Chunk (H.Chunks (Chunk), Budget);
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
      H.Gray_Head := No_Object;
   end Clear;

end Pyro.Heap;
