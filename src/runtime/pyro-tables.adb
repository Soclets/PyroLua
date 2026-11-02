--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  Lua tables: an array part for the integer keys 1 .. N, and a hash part with open
--  addressing for the other keys.

with Ada.Unchecked_Deallocation;

package body Pyro.Tables with SPARK_Mode => On is

   procedure Free_Items is new Ada.Unchecked_Deallocation (Value_Array, Value_Array_Access);
   procedure Free_Nodes is new Ada.Unchecked_Deallocation (Node_Array, Node_Array_Access);

   ----------------------------------------------------------------------------------------
   --  Keys and probe sequences
   ----------------------------------------------------------------------------------------

   --  The hash of a key: the seeded SipHash of its bits, kind and handle. A string key hashes
   --  by its handle, which is enough because strings are interned.
   function Key_Hash (S : Pyro.Strings.Seed; Key : Value) return Unsigned_64
   is (Pyro.Strings.Hash_Words
         (S, Key.Bits,
          Shift_Left (Unsigned_64 (Value_Kind'Pos (Key.Kind)), 32) or Unsigned_64 (Key.Object)));
   --  Proofs only compare hashes: the bit operations stay out of them, which they would
   --  otherwise unfold into every invariant that mentions a hash.
   pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Key_Hash);

   --  Key belongs to the array part A (whose first place is 1).
   function In_Array (A : Value_Array; Key : Value) return Boolean
   is (Key.Kind = Integer_Value
       and then A'First = 1
       and then Integer_Of (Key) in 1 .. Integer_64 (A'Last));

   --  The place of Key in the array part.
   function Index_Of (A : Value_Array; Key : Value) return Positive
   is (Positive (Integer_Of (Key)))
   with Pre => In_Array (A, Key), Post => Index_Of'Result in A'Range;

   --  The node where the probe sequence of Hash starts, in a hash part of Length nodes. The
   --  probe geometry depends on the length only, so that parts of the same length share it.
   function Home (Length : Natural; Hash : Unsigned_64) return Natural
   is (if Length = 0 then 0 else Natural (Hash and Unsigned_64 (Length - 1)) mod Length)
   with Pre => Length <= Maximum_Capacity, Post => Length = 0 or else Home'Result < Length;
   pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Home);

   --  The node Step places after From, wrapping around.
   function Step_At (Length, From, Step : Natural) return Natural
   is (if From < Length and then Step < Length
       then (if From + Step < Length then From + Step else From + Step - Length)
       else 0)
   with
     Pre  => Length <= Maximum_Capacity,
     Post => Length = 0 or else Step_At'Result < Length;

   --  How many places after From node To is, wrapping around.
   function Distance (Length, From, To : Natural) return Natural
   is (if From < Length and then To < Length
       then (if To >= From then To - From else To + (Length - From))
       else 0)
   with
     Pre  => Length <= Maximum_Capacity,
     Post =>
       (if From < Length and then To < Length
        then Distance'Result < Length and then Step_At (Length, From, Distance'Result) = To);

   --  [proof] No empty node lies on the probe sequence of node I's key before node I: a
   --  lookup that stops at the first empty node reaches it.
   function Findable (N : Node_Array; I : Natural) return Boolean
   is (N'First = 0
       and then I < N'Length
       and then N'Length <= Maximum_Capacity
       and then (for all Step in 0 .. Distance (N'Length, Home (N'Length, N (I).Hash), I) - 1 =>
                   N (Step_At (N'Length, Home (N'Length, N (I).Hash), Step)).State
                   /= Empty_Node))
   with Ghost;
   pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Findable);

   --  [proof] Node I holds what its state says, its key belongs in the hash part, and it can
   --  be found.
   function Node_Facts
     (A : Value_Array; N : Node_Array; S : Pyro.Strings.Seed; I : Natural) return Boolean
   is (I in N'Range
       and then (if N (I).State = Empty_Node then N (I).Item = Nil
       else Is_Key (N (I).Key)
            and then Is_Canonical (N (I).Key)
            and then N (I).Hash = Key_Hash (S, N (I).Key)
            and then not In_Array (A, N (I).Key)
            and then Findable (N, I)
            and then (if N (I).State = Used_Node
                      then N (I).Item /= Nil and then Is_Canonical (N (I).Item)
                      else N (I).Item = Nil)))
   with Ghost;

   --  Node_Facts, opaque: the invariant quantifies over it, and lemmas unfold it one node at a
   --  time (an unfolded quantifier body is too large for the provers to instantiate).
   function Node_Valid
     (A : Value_Array; N : Node_Array; S : Pyro.Strings.Seed; I : Natural) return Boolean
   is (Node_Facts (A, N, S, I))
   with Ghost;
   pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Node_Valid);

   --  [proof] No key is in two nodes.
   function Unique (N : Node_Array) return Boolean
   is (for all I in N'Range =>
         (for all J in N'Range =>
            (if I /= J and then N (I).State /= Empty_Node and then N (J).State /= Empty_Node
             then N (I).Key /= N (J).Key)))
   with Ghost;
   pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Unique);

   --  [proof] Every node holding a key holds its hash and can be found: what a lookup needs.
   function Nodes_Findable (N : Node_Array; S : Pyro.Strings.Seed) return Boolean
   is (N'First = 0
       and then (for all I in N'Range =>
                   (if N (I).State /= Empty_Node
                    then N (I).Hash = Key_Hash (S, N (I).Key) and then Findable (N, I))))
   with Ghost;

   --  [proof] The parts of a valid table.
   function Parts_Valid (A : Value_Array; N : Node_Array; S : Pyro.Strings.Seed) return Boolean
   is (A'First = 1
       and then A'Length <= Maximum_Array_Size
       and then N'First = 0
       and then (for all I in A'Range => Is_Canonical (A (I)))
       and then (for all I in N'Range => Node_Valid (A, N, S, I))
       and then (N'Length = 0 or else Unique (N)))
   with Ghost;

   --  A table owns both parts (each possibly empty), or neither (it is released, and empty).
   function Is_Valid (T : Table) return Boolean
   is (if T.Items = null or else T.Nodes = null then T.Items = null and then T.Nodes = null
       else Parts_Valid (T.Items.all, T.Nodes.all, T.Seed));

   ----------------------------------------------------------------------------------------
   --  Lemmas
   ----------------------------------------------------------------------------------------

   --  [proof] Node I's key is in no other node.
   procedure Lemma_Unique (N : Node_Array; I : Natural)
   with
     Ghost,
     Global => null,
     Pre    => Unique (N) and then I in N'Range and then N (I).State /= Empty_Node,
     Post   =>
       (for all J in N'Range =>
          (if J /= I and then N (J).State /= Empty_Node then N (J).Key /= N (I).Key))
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Unique);
   begin
      null;
   end Lemma_Unique;

   --  [proof] Node I of the parts of a valid table is valid, and place I of the array part
   --  holds a canonical value.
   --  [proof] What a valid node holds.
   procedure Lemma_Node_Facts
     (A : Value_Array; N : Node_Array; S : Pyro.Strings.Seed; I : Natural)
   with
     Ghost,
     Global => null,
     Pre    => Node_Valid (A, N, S, I),
     Post   => Node_Facts (A, N, S, I)
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Node_Valid);
   begin
      null;
   end Lemma_Node_Facts;

   procedure Lemma_Node (A : Value_Array; N : Node_Array; S : Pyro.Strings.Seed; I : Natural)
   with
     Ghost,
     Global => null,
     Pre    => Parts_Valid (A, N, S) and then I in N'Range,
     Post   => Node_Valid (A, N, S, I) and then Node_Facts (A, N, S, I)
   is
   begin
      pragma Assert (Node_Valid (A, N, S, I));
      Lemma_Node_Facts (A, N, S, I);
   end Lemma_Node;

   --  [proof] Node I with the facts of a valid node is valid.
   procedure Lemma_Make_Node
     (A : Value_Array; N : Node_Array; S : Pyro.Strings.Seed; I : Natural)
   with
     Ghost,
     Global => null,
     Pre    => Node_Facts (A, N, S, I),
     Post   => Node_Valid (A, N, S, I)
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Node_Valid);
   begin
      null;
   end Lemma_Make_Node;

   --  [proof] A valid node stays valid in parts with the same bounds where it holds the same
   --  and can still be found.
   procedure Lemma_Copy_Node
     (A1 : Value_Array; N1 : Node_Array; A2 : Value_Array; N2 : Node_Array;
      S  : Pyro.Strings.Seed; I : Natural)
   with
     Ghost,
     Global => null,
     Pre    =>
       Node_Valid (A1, N1, S, I)
       and then A2'First = A1'First
       and then A2'Last = A1'Last
       and then I in N2'Range
       and then N2 (I) = N1 (I)
       and then (N2 (I).State = Empty_Node or else Findable (N2, I)),
     Post   => Node_Valid (A2, N2, S, I)
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Node_Valid);
   begin
      null;
   end Lemma_Copy_Node;

   procedure Lemma_Item (A : Value_Array; N : Node_Array; S : Pyro.Strings.Seed; I : Positive)
   with
     Ghost,
     Global => null,
     Pre    => Parts_Valid (A, N, S) and then I in A'Range,
     Post   => Is_Canonical (A (I))
   is
   begin
      null;
   end Lemma_Item;

   --  [proof] Parts with no key are valid.
   procedure Lemma_Empty_Parts (A : Value_Array; N : Node_Array; S : Pyro.Strings.Seed)
   with
     Ghost,
     Global => null,
     Pre    =>
       A'First = 1
       and then A'Length <= Maximum_Array_Size
       and then N'First = 0
       and then (for all I in A'Range => A (I) = Nil)
       and then (for all I in N'Range => N (I) = (State => Empty_Node, Key => Nil, Hash => 0,
                                                     Item => Nil)),
     Post   => Parts_Valid (A, N, S)
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Unique);
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Node_Valid);
   begin
      null;
   end Lemma_Empty_Parts;

   --  [proof] The parts of a valid table give a lookup what it needs.
   procedure Lemma_Findable (A : Value_Array; N : Node_Array; S : Pyro.Strings.Seed)
   with
     Ghost,
     Global => null,
     Pre    => Parts_Valid (A, N, S),
     Post   => Nodes_Findable (N, S)
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Node_Valid);
   begin
      null;
   end Lemma_Findable;

   --  [proof] A probe from the home of node I's hash that meets an empty node at step Stop
   --  has passed node I.
   procedure Lemma_Passed (N : Node_Array; I, Stop : Natural)
   with
     Ghost,
     Global => null,
     Pre    =>
       N'First = 0 and then I < N'Length and then Stop < N'Length
       and then Findable (N, I)
       and then N (I).State /= Empty_Node
       and then N (Step_At (N'Length, Home (N'Length, N (I).Hash), Stop)).State = Empty_Node,
     Post   => Distance (N'Length, Home (N'Length, N (I).Hash), I) < Stop
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Findable);
   begin
      null;
   end Lemma_Passed;

   ----------------------------------------------------------------------------------------
   --  The model
   ----------------------------------------------------------------------------------------

   --  [proof] Some used node holds Key.
   function Holds (N : Node_Array; Key : Value) return Boolean
   is (for some I in N'Range => N (I).State = Used_Node and then N (I).Key = Key)
   with Ghost;

   --  [proof] Key is the key of a place of A that is not nil.
   function Array_Key (A : Value_Array; Key : Value) return Boolean
   is (In_Array (A, Key)
       and then A (Index_Of (A, Key)) /= Nil
       and then Key = Integer_Value_Of (Integer_64 (Index_Of (A, Key))))
   with Ghost;

   --  [proof] The contents of parts A and N: the places of A that are not nil, and the keys of
   --  the used nodes.
   function Model_Of (A : Value_Array; N : Node_Array; S : Pyro.Strings.Seed)
     return Value_Maps.Map
   with
     Ghost,
     Global => null,
     Pre    => Parts_Valid (A, N, S),
     Post   =>
       (for all I in A'Range =>
          Value_Maps.Has_Key (Model_Of'Result, Integer_Value_Of (Integer_64 (I))) = (A (I) /= Nil)
          and then (if A (I) /= Nil
                    then Value_Maps.Get (Model_Of'Result, Integer_Value_Of (Integer_64 (I)))
                         = A (I)))
       and then (for all I in N'Range =>
                   (if N (I).State = Used_Node
                    then Value_Maps.Has_Key (Model_Of'Result, N (I).Key)
                         and then Value_Maps.Get (Model_Of'Result, N (I).Key) = N (I).Item))
       and then (for all Key of Model_Of'Result =>
                   (Array_Key (A, Key) or else Holds (N, Key))
                   and then Value_Maps.Get (Model_Of'Result, Key) /= Nil)
   is
      Result : Value_Maps.Map;
   begin
      for I in A'Range loop
         if A (I) /= Nil then
            Result := Value_Maps.Add (Result, Integer_Value_Of (Integer_64 (I)), A (I));
         end if;
         pragma Loop_Invariant
           (for all J in A'First .. I =>
              Value_Maps.Has_Key (Result, Integer_Value_Of (Integer_64 (J))) = (A (J) /= Nil)
              and then (if A (J) /= Nil
                        then Value_Maps.Get (Result, Integer_Value_Of (Integer_64 (J))) = A (J)));
         pragma Loop_Invariant
           (for all Key of Result =>
              Array_Key (A, Key)
              and then Index_Of (A, Key) <= I
              and then Value_Maps.Get (Result, Key) /= Nil);
      end loop;
      for I in N'Range loop
         if N (I).State = Used_Node then
            Lemma_Node (A, N, S, I);
            Lemma_Unique (N, I);
            Result := Value_Maps.Add (Result, N (I).Key, N (I).Item);
         end if;
         pragma Loop_Invariant
           (for all J in A'Range =>
              Value_Maps.Has_Key (Result, Integer_Value_Of (Integer_64 (J))) = (A (J) /= Nil)
              and then (if A (J) /= Nil
                        then Value_Maps.Get (Result, Integer_Value_Of (Integer_64 (J))) = A (J)));
         pragma Loop_Invariant
           (for all J in N'First .. I =>
              (if N (J).State = Used_Node
               then Value_Maps.Has_Key (Result, N (J).Key)
                    and then Value_Maps.Get (Result, N (J).Key) = N (J).Item));
         pragma Loop_Invariant
           (for all Key of Result =>
              (Array_Key (A, Key)
               or else (for some J in N'First .. I =>
                          N (J).State = Used_Node and then N (J).Key = Key))
              and then Value_Maps.Get (Result, Key) /= Nil);
      end loop;
      return Result;
   end Model_Of;

   function Model (T : Table) return Value_Maps.Map
   is (if T.Items /= null and then T.Nodes /= null
          and then Parts_Valid (T.Items.all, T.Nodes.all, T.Seed)
       then Model_Of (T.Items.all, T.Nodes.all, T.Seed)
       else Value_Maps.Empty_Map);

   ----------------------------------------------------------------------------------------
   --  Lookups
   ----------------------------------------------------------------------------------------

   --  The node holding Key (used or dead), or -1.
   function Find (N : Node_Array; S : Pyro.Strings.Seed; Key : Value) return Integer
   with
     Global => null,
     Pre    => Nodes_Findable (N, S),
     Post   =>
       (if Find'Result >= 0
        then Find'Result in N'Range
             and then N (Find'Result).State /= Empty_Node
             and then N (Find'Result).Key = Key
        else Find'Result = -1
             and then (for all I in N'Range => N (I).State = Empty_Node or else N (I).Key /= Key))
   is
      Start    : constant Natural := Home (N'Length, Key_Hash (S, Key));
      Position : Natural;
   begin
      if N'Length = 0 then
         return -1;
      end if;
      for Step in 0 .. N'Length - 1 loop
         Position := Step_At (N'Length, Start, Step);
         if N (Position).State = Empty_Node then
            --  Every node holding Key would have been met before this one.
            for I in N'Range loop
               if N (I).State /= Empty_Node and then N (I).Key = Key then
                  Lemma_Passed (N, I, Step);
                  pragma Assert (False);
               end if;
               pragma Loop_Invariant
                 (for all J in N'First .. I => N (J).State = Empty_Node or else N (J).Key /= Key);
            end loop;
            return -1;
         elsif N (Position).Key = Key then
            return Position;
         end if;
         pragma Loop_Invariant
           (for all Earlier in 0 .. Step =>
              N (Step_At (N'Length, Start, Earlier)).State /= Empty_Node
              and then N (Step_At (N'Length, Start, Earlier)).Key /= Key);
      end loop;
      --  Every node was met.
      for I in N'Range loop
         pragma Assert (Step_At (N'Length, Start, Distance (N'Length, Start, I)) = I);
         pragma Loop_Invariant
           (for all J in N'First .. I => N (J).State = Empty_Node or else N (J).Key /= Key);
      end loop;
      return -1;
   end Find;

   function Get (T : Table; Key : Value) return Value is
      K        : constant Value := Key_Of (Key);
      Position : Integer;
   begin
      if K = Nil or else T.Items = null or else T.Nodes = null then
         return Nil;
      end if;
      pragma Assert (Model (T) = Model_Of (T.Items.all, T.Nodes.all, T.Seed));
      if In_Array (T.Items.all, K) then
         Lemma_Integer_Value (K);
         pragma Assert (K = Integer_Value_Of (Integer_64 (Index_Of (T.Items.all, K))));
         Lemma_Item (T.Items.all, T.Nodes.all, T.Seed, Index_Of (T.Items.all, K));
         return T.Items (Index_Of (T.Items.all, K));
      end if;
      Lemma_Findable (T.Items.all, T.Nodes.all, T.Seed);
      Position := Find (T.Nodes.all, T.Seed, K);
      if Position < 0 then
         pragma Assert (not Holds (T.Nodes.all, K));
         return Nil;
      end if;
      Lemma_Node (T.Items.all, T.Nodes.all, T.Seed, Position);
      if T.Nodes (Position).State = Used_Node then
         return T.Nodes (Position).Item;
      end if;
      --  A dead node: its key is in no used node.
      Lemma_Unique (T.Nodes.all, Position);
      pragma Assert (not Holds (T.Nodes.all, K));
      return Nil;
   end Get;

   ----------------------------------------------------------------------------------------
   --  The values a table holds
   ----------------------------------------------------------------------------------------

   --  [proof] Entry Position of parts A and N: the places of A, then the keys of the nodes
   --  (nil for empty nodes), then their items.
   function Entry_Of (A : Value_Array; N : Node_Array; Position : Positive) return Value
   is (if A'Length > Maximum_Array_Size or else N'Length > Maximum_Capacity
          or else Position > A'Length + 2 * N'Length
       then Nil
       elsif Position <= A'Length then A (A'First - 1 + Position)
       elsif Position <= A'Length + N'Length
       then (if N (N'First + (Position - A'Length - 1)).State = Empty_Node then Nil
             else N (N'First + (Position - A'Length - 1)).Key)
       else N (N'First + (Position - A'Length - N'Length - 1)).Item);
   --  Proofs about entries go through the lemmas below, which say where each value is.
   pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Entry_Of);

   --  [proof] Where the values of parts A and N are among their entries.
   procedure Lemma_Entry_Places (A : Value_Array; N : Node_Array)
   with
     Ghost,
     Global => null,
     Pre    =>
       A'First = 1
       and then N'First = 0
       and then A'Length <= Maximum_Array_Size
       and then N'Length <= Maximum_Capacity,
     Post   =>
       (for all I in A'Range => Entry_Of (A, N, I) = A (I))
       and then (for all J in N'Range =>
                   Entry_Of (A, N, A'Length + 1 + J)
                   = (if N (J).State = Empty_Node then Nil else N (J).Key)
                   and then Entry_Of (A, N, A'Length + N'Length + 1 + J) = N (J).Item)
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Entry_Of);
   begin
      null;
   end Lemma_Entry_Places;

   --  [proof] Parts with nothing in them hold no value.
   procedure Lemma_Empty_Entries (A : Value_Array; N : Node_Array)
   with
     Ghost,
     Global => null,
     Pre    =>
       A'First = 1
       and then N'First = 0
       and then A'Length <= Maximum_Array_Size
       and then N'Length <= Maximum_Capacity
       and then (for all I in A'Range => A (I) = Nil)
       and then (for all J in N'Range => N (J).State = Empty_Node and then N (J).Item = Nil),
     Post   =>
       (for all Position in 1 .. A'Length + 2 * N'Length => Entry_Of (A, N, Position) = Nil)
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Entry_Of);
   begin
      null;
   end Lemma_Empty_Entries;

   function Entries_Of (A : Value_Array; N : Node_Array) return Value_Sequences.Sequence
   with
     Ghost,
     Global => null,
     Pre    => A'Length <= Maximum_Array_Size and then N'Length <= Maximum_Capacity,
     Post   =>
       Value_Sequences.Last (Entries_Of'Result) = A'Length + 2 * N'Length
       and then (for all Position in 1 .. A'Length + 2 * N'Length =>
                   Value_Sequences.Get (Entries_Of'Result, Position)
                   = Entry_Of (A, N, Position))
   is
      Result : Value_Sequences.Sequence;
   begin
      for Position in 1 .. A'Length + 2 * N'Length loop
         Result := Value_Sequences.Add (Result, Entry_Of (A, N, Position));
         pragma Loop_Invariant (Value_Sequences.Last (Result) = Position);
         pragma Loop_Invariant
           (for all Earlier in 1 .. Position =>
              Value_Sequences.Get (Result, Earlier) = Entry_Of (A, N, Earlier));
      end loop;
      return Result;
   end Entries_Of;

   --  [proof] Parts A2, N2 hold the values of parts A1, N1 (of the same lengths) at every
   --  place, except places that hold Key, Item, or no object.
   function Same_Entries
     (A1 : Value_Array; N1 : Node_Array; A2 : Value_Array; N2 : Node_Array; Key, Item : Value)
      return Boolean
   is (A1'Length <= Maximum_Array_Size
       and then N1'Length <= Maximum_Capacity
       and then A2'Length = A1'Length
       and then N2'Length = N1'Length
       and then (for all Position in 1 .. A1'Length + 2 * N1'Length =>
                   Entry_Of (A2, N2, Position).Kind /= Object_Value
                   or else Entry_Of (A2, N2, Position) = Key
                   or else Entry_Of (A2, N2, Position) = Item
                   or else Entry_Of (A2, N2, Position) = Entry_Of (A1, N1, Position)))
   with Ghost;

   --  [proof] A sequence contains each of its elements.
   procedure Lemma_Contains (S : Value_Sequences.Sequence; Position : Positive)
   with
     Ghost,
     Global => null,
     Pre    => Position <= Value_Sequences.Last (S),
     Post   =>
       Value_Sequences.Contains
         (S, 1, Value_Sequences.Last (S), Value_Sequences.Get (S, Position))
   is
   begin
      null;
   end Lemma_Contains;

   --  [proof] What Same_Entries says of parts, Entries_From says of their entries.
   procedure Lemma_Entries
     (A1 : Value_Array; N1 : Node_Array; A2 : Value_Array; N2 : Node_Array; Key, Item : Value)
   with
     Ghost,
     Global => null,
     Pre    => Same_Entries (A1, N1, A2, N2, Key, Item),
     Post   => Entries_From (Entries_Of (A2, N2), Entries_Of (A1, N1), Key, Item)
   is
      Before : constant Value_Sequences.Sequence := Entries_Of (A1, N1);
      After  : constant Value_Sequences.Sequence := Entries_Of (A2, N2);
   begin
      for Position in 1 .. A1'Length + 2 * N1'Length loop
         pragma Assert (Value_Sequences.Get (After, Position) = Entry_Of (A2, N2, Position));
         pragma Assert (Value_Sequences.Get (Before, Position) = Entry_Of (A1, N1, Position));
         if Entry_Of (A2, N2, Position).Kind = Object_Value
           and then Entry_Of (A2, N2, Position) /= Key
           and then Entry_Of (A2, N2, Position) /= Item
         then
            pragma Assert (Entry_Of (A2, N2, Position) = Entry_Of (A1, N1, Position));
            Lemma_Contains (Before, Position);
            pragma Assert
              (Value_Sequences.Contains
                 (Before, 1, Value_Sequences.Last (Before), Value_Sequences.Get (After, Position)));
         end if;
         pragma Loop_Invariant
           (for all Earlier in 1 .. Position =>
              Value_Sequences.Get (After, Earlier).Kind /= Object_Value
              or else Value_Sequences.Get (After, Earlier) = Key
              or else Value_Sequences.Get (After, Earlier) = Item
              or else Value_Sequences.Contains
                        (Before, 1, Value_Sequences.Last (Before),
                         Value_Sequences.Get (After, Earlier)));
      end loop;
   end Lemma_Entries;

   --  [proof] Objects of Third come from Second, or are Key or Item; objects of Second come
   --  from First; so objects of Third come from First, or are Key or Item.
   procedure Lemma_Entries_Chain
     (First, Second, Third : Value_Sequences.Sequence; Key, Item : Value)
   with
     Ghost,
     Global => null,
     Pre    =>
       Entries_From (Second, First, Nil, Nil) and then Entries_From (Third, Second, Key, Item),
     Post   => Entries_From (Third, First, Key, Item)
   is
   begin
      null;
   end Lemma_Entries_Chain;

   ----------------------------------------------------------------------------------------
   --  Changing the parts
   ----------------------------------------------------------------------------------------

   --  [proof] The steps of a probe sequence reach different nodes, and Distance undoes them.
   procedure Lemma_Steps (Length, From, Step : Natural)
   with
     Ghost,
     Global => null,
     Pre    => Length <= Maximum_Capacity and then From < Length and then Step < Length,
     Post   =>
       Distance (Length, From, Step_At (Length, From, Step)) = Step
       and then (for all Other in 0 .. Length - 1 =>
                   (if Other /= Step
                    then Step_At (Length, From, Other) /= Step_At (Length, From, Step)))
   is
   begin
      null;
   end Lemma_Steps;

   --  [proof] After holds the same keys as Before in the same nodes: they differ at most in
   --  the items, and in which keys are used or dead.
   function Same_Keys (Before, After : Node_Array) return Boolean
   is (After'First = Before'First
       and then After'Last = Before'Last
       and then (for all I in Before'Range =>
                   (Before (I).State = Empty_Node) = (After (I).State = Empty_Node)
                   and then After (I).Key = Before (I).Key
                   and then After (I).Hash = Before (I).Hash))
   with Ghost;

   procedure Lemma_Same_Keys (Before, After : Node_Array)
   with
     Ghost,
     Global => null,
     Pre    => Before'First = 0 and then Same_Keys (Before, After),
     Post   =>
       (for all I in After'Range => Findable (After, I) = Findable (Before, I))
       and then (Before'Length = 0 or else Unique (After) = Unique (Before))
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Findable);
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Unique);
   begin
      null;
   end Lemma_Same_Keys;

   --  [proof] Filling node P keeps every other node findable.
   procedure Lemma_Fill (Before, After : Node_Array; P : Natural)
   with
     Ghost,
     Global => null,
     Pre    =>
       Before'First = 0
       and then After'First = 0
       and then After'Last = Before'Last
       and then P in Before'Range
       and then After (P).State /= Empty_Node
       and then (for all I in Before'Range => (if I /= P then After (I) = Before (I))),
     Post   =>
       (for all I in After'Range =>
          (if I /= P and then Findable (Before, I) then Findable (After, I)))
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Findable);
   begin
      null;
   end Lemma_Fill;

   --  [proof] Place I of the array part becomes Item.
   procedure Lemma_Store_Item
     (Before, After : Value_Array; N : Node_Array; S : Pyro.Strings.Seed; I : Positive;
      Item          : Value)
   with
     Ghost,
     Global => null,
     Pre    =>
       Parts_Valid (Before, N, S)
       and then After'First = Before'First
       and then After'Last = Before'Last
       and then I in Before'Range
       and then Is_Canonical (Item)
       and then After (I) = Item
       and then (for all J in Before'Range => (if J /= I then After (J) = Before (J))),
     Post   =>
       Parts_Valid (After, N, S)
       and then Stored
                  (Model_Of (After, N, S), Model_Of (Before, N, S),
                   Integer_Value_Of (Integer_64 (I)), Item)
       and then Same_Entries (Before, N, After, N, Integer_Value_Of (Integer_64 (I)), Item)
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Entry_Of);
   begin
      for J in N'Range loop
         Lemma_Node (Before, N, S, J);
         Lemma_Copy_Node (Before, N, After, N, S, J);
         pragma Loop_Invariant
           (for all Earlier in N'First .. J => Node_Valid (After, N, S, Earlier));
      end loop;
      pragma Assert (Parts_Valid (After, N, S));
   end Lemma_Store_Item;

   --  [proof] The key of node P keeps its node, which takes Item (and is dead when Item is
   --  nil).
   procedure Lemma_Store_Node
     (A : Value_Array; Before, After : Node_Array; S : Pyro.Strings.Seed; P : Natural;
      Item : Value)
   with
     Ghost,
     Global => null,
     Pre    =>
       Parts_Valid (A, Before, S)
       and then P in Before'Range
       and then Before (P).State /= Empty_Node
       and then Is_Canonical (Item)
       and then After'First = Before'First
       and then After'Last = Before'Last
       and then After (P)
                = (State => (if Item = Nil then Dead_Node else Used_Node),
                   Key   => Before (P).Key,
                   Hash  => Before (P).Hash,
                   Item  => Item)
       and then (for all J in Before'Range => (if J /= P then After (J) = Before (J))),
     Post   =>
       Parts_Valid (A, After, S)
       and then Stored (Model_Of (A, After, S), Model_Of (A, Before, S), Before (P).Key, Item)
       and then Same_Entries (A, Before, A, After, Before (P).Key, Item)
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Entry_Of);
   begin
      Lemma_Same_Keys (Before, After);
      Lemma_Unique (Before, P);
      for J in After'Range loop
         Lemma_Node (A, Before, S, J);
         if J = P then
            Lemma_Make_Node (A, After, S, J);
         else
            Lemma_Copy_Node (A, Before, A, After, S, J);
         end if;
         pragma Loop_Invariant
           (for all Earlier in After'First .. J => Node_Valid (A, After, S, Earlier));
      end loop;
      pragma Assert (Parts_Valid (A, After, S));
      Lemma_Node (A, Before, S, P);
      Lemma_Unique (After, P);
      if Item = Nil then
         pragma Assert (not Holds (After, Before (P).Key));
      end if;
   end Lemma_Store_Node;

   --  [proof] A node filled at the first node of its probe sequence that is not used can be
   --  found.
   procedure Lemma_Insert_Findable
     (Before, After : Node_Array; P, Step : Natural; Hash : Unsigned_64)
   with
     Ghost,
     Global => null,
     Pre    =>
       Before'First = 0
       and then Before'Length >= 1
       and then Step < Before'Length
       and then P = Step_At (Before'Length, Home (Before'Length, Hash), Step)
       and then (for all Earlier in 0 .. Step - 1 =>
                   Before (Step_At (Before'Length, Home (Before'Length, Hash), Earlier)).State
                   = Used_Node)
       and then After'First = 0
       and then After'Last = Before'Last
       and then After (P).Hash = Hash
       and then (for all J in Before'Range => (if J /= P then After (J) = Before (J))),
     Post   => Findable (After, P)
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Findable);
   begin
      Lemma_Steps (Before'Length, Home (Before'Length, Hash), Step);
   end Lemma_Insert_Findable;

   --  [proof] A key in no node, put in node P, leaves every key in one node.
   procedure Lemma_Insert_Unique (Before, After : Node_Array; P : Natural)
   with
     Ghost,
     Global => null,
     Pre    =>
       Before'Length >= 1
       and then Unique (Before)
       and then P in Before'Range
       and then After'First = Before'First
       and then After'Last = Before'Last
       and then After (P).State /= Empty_Node
       and then (for all I in Before'Range =>
                   Before (I).State = Empty_Node or else Before (I).Key /= After (P).Key)
       and then (for all J in Before'Range => (if J /= P then After (J) = Before (J))),
     Post   => Unique (After)
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Unique);
   begin
      null;
   end Lemma_Insert_Unique;

   --  [proof] New key Key, in no node and not in the array part, takes node P, the first node
   --  of its probe sequence that is not used (Step steps from its home).
   procedure Lemma_Insert
     (A : Value_Array; Before, After : Node_Array; S : Pyro.Strings.Seed; P, Step : Natural;
      Key, Item : Value)
   with
     Ghost,
     Global => null,
     Pre    =>
       Parts_Valid (A, Before, S)
       and then Before'Length >= 1
       and then Is_Key (Key)
       and then Is_Canonical (Key)
       and then not In_Array (A, Key)
       and then Item /= Nil
       and then Is_Canonical (Item)
       and then (for all I in Before'Range =>
                   Before (I).State = Empty_Node or else Before (I).Key /= Key)
       and then Step < Before'Length
       and then P = Step_At (Before'Length, Home (Before'Length, Key_Hash (S, Key)), Step)
       and then (for all Earlier in 0 .. Step - 1 =>
                   Before (Step_At (Before'Length, Home (Before'Length, Key_Hash (S, Key)),
                                    Earlier)).State
                   = Used_Node)
       and then Before (P).State /= Used_Node
       and then After'First = 0
       and then After'Last = Before'Last
       and then After (P)
                = (State => Used_Node, Key => Key, Hash => Key_Hash (S, Key), Item => Item)
       and then (for all J in Before'Range => (if J /= P then After (J) = Before (J))),
     Post   =>
       Parts_Valid (A, After, S)
       and then Stored (Model_Of (A, After, S), Model_Of (A, Before, S), Key, Item)
       and then Same_Entries (A, Before, A, After, Key, Item)
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Entry_Of);
   begin
      Lemma_Insert_Findable (Before, After, P, Step, Key_Hash (S, Key));
      Lemma_Fill (Before, After, P);
      Lemma_Insert_Unique (Before, After, P);
      for J in After'Range loop
         if J = P then
            Lemma_Make_Node (A, After, S, J);
         else
            Lemma_Node (A, Before, S, J);
            Lemma_Copy_Node (A, Before, A, After, S, J);
         end if;
         pragma Loop_Invariant
           (for all Earlier in After'First .. J => Node_Valid (A, After, S, Earlier));
      end loop;
      pragma Assert (Parts_Valid (A, After, S));
      pragma Assert (not Holds (Before, Key));
      Lemma_Unique (After, P);
   end Lemma_Insert;

   function Entry_Count (T : Table) return Natural
   is (if T.Items = null or else T.Nodes = null
          or else T.Items'Length > Maximum_Array_Size or else T.Nodes'Length > Maximum_Capacity
       then 0
       else T.Items'Length + 2 * T.Nodes'Length);

   function Entry_At (T : Table; Position : Positive) return Value
   is (Entry_Of (T.Items.all, T.Nodes.all, Position));

   function Entries (T : Table) return Value_Sequences.Sequence
   is (if T.Items = null or else T.Nodes = null
          or else T.Items'Length > Maximum_Array_Size or else T.Nodes'Length > Maximum_Capacity
       then Value_Sequences.Empty_Sequence
       else Entries_Of (T.Items.all, T.Nodes.all));

   ----------------------------------------------------------------------------------------
   --  Setting
   ----------------------------------------------------------------------------------------

   procedure Set_Seed (T : in out Table; Key : Pyro.Strings.Seed) is
   begin
      T.Seed := Key;
   end Set_Seed;

   --  The nodes a hash part needs for Keys keys, below three quarters of them: none for no
   --  key, otherwise a power of two of at least 4.
   function Capacity_For (Keys : Natural) return Natural
   with
     Global => null,
     Pre    => Keys <= Maximum_Capacity / 2,
     Post   => Capacity_For'Result <= Maximum_Capacity
   is
      Result : Natural := 4;
   begin
      if Keys = 0 then
         return 0;
      end if;
      while Result <= Maximum_Capacity / 2 and then Result / 4 * 3 <= Keys loop
         pragma Loop_Variant (Increases => Result);
         pragma Loop_Invariant (Result in 4 .. Maximum_Capacity / 2);
         Result := Result * 2;
      end loop;
      return Result;
   end Capacity_For;

   --  [proof] No node of N is dead: parts being built.
   function No_Dead (N : Node_Array) return Boolean
   is (for all I in N'Range => N (I).State /= Dead_Node)
   with Ghost;

   --  Puts Key, which the parts being built do not hold, with Item: in the array part when it
   --  belongs there, otherwise in the first empty node of its probe sequence. Placed is False,
   --  and the parts unchanged, when every node is used.
   procedure Place
     (A      : in out Value_Array;
      N      : in out Node_Array;
      S      : Pyro.Strings.Seed;
      Key    : Value;
      Item   : Value;
      Placed : out Boolean)
   with
     Global => null,
     Pre    =>
       Parts_Valid (A, N, S)
       and then No_Dead (N)
       and then Is_Key (Key)
       and then Is_Canonical (Key)
       and then Item /= Nil
       and then Is_Canonical (Item)
       and then not Value_Maps.Has_Key (Model_Of (A, N, S), Key),
     Post   =>
       Parts_Valid (A, N, S)
       and then No_Dead (N)
       and then A'First = A'First'Old
       and then A'Last = A'Last'Old
       and then N'First = N'First'Old
       and then N'Last = N'Last'Old
       and then (if Placed then Stored (Model_Of (A, N, S), Model_Of (A, N, S)'Old, Key, Item)
                 else Model_Of (A, N, S) = Model_Of (A, N, S)'Old)
       and then Same_Entries (A'Old, N'Old, A, N, Key, Item)
   is
      Hash  : constant Unsigned_64 := Key_Hash (S, Key);
      Start : constant Natural := Home (N'Length, Hash);
      Spot  : Natural := 0;
      Found : Integer := -1;
   begin
      Placed := False;
      if In_Array (A, Key) then
         declare
            Before : constant Value_Array := A with Ghost;
            Index  : constant Positive := Index_Of (A, Key);
         begin
            Lemma_Integer_Value (Key);
            A (Index) := Item;
            Lemma_Store_Item (Before, A, N, S, Index, Item);
         end;
         Placed := True;
         return;
      end if;
      pragma Assert (for all I in N'Range => N (I).State = Empty_Node or else N (I).Key /= Key);
      if N'Length = 0 then
         return;
      end if;
      for Step in 0 .. N'Length - 1 loop
         Spot := Step_At (N'Length, Start, Step);
         if N (Spot).State = Empty_Node then
            Found := Step;
            exit;
         end if;
         pragma Loop_Invariant
           (for all Earlier in 0 .. Step =>
              N (Step_At (N'Length, Start, Earlier)).State = Used_Node);
      end loop;
      if Found < 0 then
         return;
      end if;
      declare
         Before : constant Node_Array := N with Ghost;
      begin
         N (Spot) := (State => Used_Node, Key => Key, Hash => Hash, Item => Item);
         Lemma_Insert (A, Before, N, S, Spot, Found, Key, Item);
      end;
      Placed := True;
   end Place;

   --  Resize, with what Set needs to know of the parts it leaves.
   procedure Resize_Parts
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
       and then Entries_From (Entries (T), Entries (T)'Old, Nil, Nil)
       and then (if Success then T.Items /= null and then No_Dead (T.Nodes.all))
   is
      Capacity    : constant Natural := Capacity_For (Hash_Size);
      Cost        : constant Byte_Count :=
        Item_Bytes * Byte_Count (Array_Size) + Node_Bytes * Byte_Count (Capacity);
      Old_Model   : constant Value_Maps.Map := Model (T) with Ghost;
      Old_Entries : constant Value_Sequences.Sequence := Entries (T) with Ghost;
      Items       : Value_Array_Access;
      Nodes       : Node_Array_Access;
      Placed      : Boolean := True;
   begin
      Charge (Budget, Cost, Success);
      if not Success then
         return;
      end if;
      Items := new Value_Array'(1 .. Array_Size => Nil);
      Nodes := new Node_Array'(0 .. Capacity - 1 => (others => <>));
      Lemma_Empty_Parts (Items.all, Nodes.all, T.Seed);
      pragma Assert (Value_Maps.Is_Empty (Model_Of (Items.all, Nodes.all, T.Seed)));
      Lemma_Empty_Entries (Items.all, Nodes.all);
      if T.Items /= null then
         Lemma_Entry_Places (T.Items.all, T.Nodes.all);
         for I in T.Items'Range loop
            if T.Items (I) /= Nil then
               Lemma_Item (T.Items.all, T.Nodes.all, T.Seed, I);
               Lemma_Contains (Old_Entries, I);
               Place (Items.all, Nodes.all, T.Seed, Integer_Value_Of (Integer_64 (I)), T.Items (I),
                      Placed);
               exit when not Placed;
            end if;
            pragma Loop_Invariant (Items /= null and then Nodes /= null);
            pragma Loop_Invariant (Items'First = 1 and then Items'Last = Array_Size);
            pragma Loop_Invariant (Nodes'First = 0 and then Nodes'Length = Capacity);
            pragma Loop_Invariant (Parts_Valid (Items.all, Nodes.all, T.Seed));
            pragma Loop_Invariant (No_Dead (Nodes.all));
            pragma Loop_Invariant (Limit (Budget) = Limit (Budget)'Loop_Entry);
            pragma Loop_Invariant
              (for all Position in 1 .. Array_Size + 2 * Capacity =>
                 Entry_Of (Items.all, Nodes.all, Position).Kind /= Object_Value
                 or else Value_Sequences.Contains
                           (Old_Entries, 1, Value_Sequences.Last (Old_Entries),
                            Entry_Of (Items.all, Nodes.all, Position)));
            pragma Loop_Invariant
              (for all Key of Model_Of (Items.all, Nodes.all, T.Seed) =>
                 Value_Maps.Has_Key (Old_Model, Key)
                 and then Value_Maps.Get (Old_Model, Key)
                          = Value_Maps.Get (Model_Of (Items.all, Nodes.all, T.Seed), Key)
                 and then Array_Key (T.Items.all, Key)
                 and then Index_Of (T.Items.all, Key) <= I);
            pragma Loop_Invariant
              (for all J in T.Items'First .. I =>
                 (if T.Items (J) /= Nil
                  then Value_Maps.Has_Key
                         (Model_Of (Items.all, Nodes.all, T.Seed),
                          Integer_Value_Of (Integer_64 (J)))));
         end loop;
      end if;
      if T.Items /= null and then Placed then
         for J in T.Nodes'Range loop
            if T.Nodes (J).State = Used_Node then
               Lemma_Node (T.Items.all, T.Nodes.all, T.Seed, J);
               Lemma_Unique (T.Nodes.all, J);
               Lemma_Contains (Old_Entries, T.Items'Length + 1 + J);
               Lemma_Contains (Old_Entries, T.Items'Length + T.Nodes'Length + 1 + J);
               Place (Items.all, Nodes.all, T.Seed, T.Nodes (J).Key, T.Nodes (J).Item, Placed);
               exit when not Placed;
            end if;
            pragma Loop_Invariant (Items /= null and then Nodes /= null);
            pragma Loop_Invariant (Items'First = 1 and then Items'Last = Array_Size);
            pragma Loop_Invariant (Nodes'First = 0 and then Nodes'Length = Capacity);
            pragma Loop_Invariant (Parts_Valid (Items.all, Nodes.all, T.Seed));
            pragma Loop_Invariant (No_Dead (Nodes.all));
            pragma Loop_Invariant (Limit (Budget) = Limit (Budget)'Loop_Entry);
            pragma Loop_Invariant
              (for all Position in 1 .. Array_Size + 2 * Capacity =>
                 Entry_Of (Items.all, Nodes.all, Position).Kind /= Object_Value
                 or else Value_Sequences.Contains
                           (Old_Entries, 1, Value_Sequences.Last (Old_Entries),
                            Entry_Of (Items.all, Nodes.all, Position)));
            pragma Loop_Invariant
              (for all Key of Model_Of (Items.all, Nodes.all, T.Seed) =>
                 Value_Maps.Has_Key (Old_Model, Key)
                 and then Value_Maps.Get (Old_Model, Key)
                          = Value_Maps.Get (Model_Of (Items.all, Nodes.all, T.Seed), Key)
                 and then (Array_Key (T.Items.all, Key)
                           or else (for some Earlier in T.Nodes'First .. J =>
                                      T.Nodes (Earlier).State = Used_Node
                                      and then T.Nodes (Earlier).Key = Key)));
            pragma Loop_Invariant
              (for all I in T.Items'Range =>
                 (if T.Items (I) /= Nil
                  then Value_Maps.Has_Key
                         (Model_Of (Items.all, Nodes.all, T.Seed),
                          Integer_Value_Of (Integer_64 (I)))));
            pragma Loop_Invariant
              (for all Earlier in T.Nodes'First .. J =>
                 (if T.Nodes (Earlier).State = Used_Node
                  then Value_Maps.Has_Key
                         (Model_Of (Items.all, Nodes.all, T.Seed), T.Nodes (Earlier).Key)));
         end loop;
      end if;
      Success := Placed;
      if not Success then
         Free_Items (Items);
         Free_Nodes (Nodes);
         Release (Budget, Cost);
         return;
      end if;
      --  The new parts hold exactly the old contents.
      pragma Assert
        (for all Key of Model_Of (Items.all, Nodes.all, T.Seed) =>
           Value_Maps.Has_Key (Old_Model, Key)
           and then Value_Maps.Get (Old_Model, Key)
                    = Value_Maps.Get (Model_Of (Items.all, Nodes.all, T.Seed), Key));
      pragma Assert
        (for all Key of Old_Model =>
           Value_Maps.Has_Key (Model_Of (Items.all, Nodes.all, T.Seed), Key));
      pragma Assert (Model_Of (Items.all, Nodes.all, T.Seed) = Old_Model);
      if T.Items /= null then
         Release (Budget, Item_Bytes * Byte_Count (T.Items'Length)
                          + Node_Bytes * Byte_Count (T.Nodes'Length));
      end if;
      Free_Items (T.Items);
      Free_Nodes (T.Nodes);
      T.Items := Items;
      T.Nodes := Nodes;
      T.Filled := 0;
   end Resize_Parts;

   procedure Resize
     (T          : in out Table;
      Budget     : in out Memory_Budget;
      Array_Size : Natural;
      Hash_Size  : Natural;
      Success    : out Boolean) is
   begin
      Resize_Parts (T, Budget, Array_Size, Hash_Size, Success);
   end Resize;

   --  [puc lobject.c:luaO_ceillog2] The smallest Log with 2 ** Log >= Value.
   function Ceiling_Log_2 (Value : Positive) return Natural
   with Global => null, Post => Ceiling_Log_2'Result <= 31
   is
      Log   : Natural := 0;
      Power : Positive := 1;
   begin
      while Power < Value and then Power <= Positive'Last / 2 loop
         pragma Loop_Variant (Increases => Power);
         pragma Loop_Invariant (Log <= 31);
         Power := Power * 2;
         if Log < 31 then
            Log := Log + 1;
         end if;
      end loop;
      return Log;
   end Ceiling_Log_2;

   --  The largest array part, as a power of two.
   Maximum_Array_Bits : constant := 26;

   --  How many integer keys of the table lie in each slice (2 ** (Bits - 1), 2 ** Bits].
   type Key_Counts is array (0 .. Maximum_Array_Bits) of Natural;

   --  [puc ltable.c:countint] Counts Key in Counts when it could go to the array part, and in
   --  Array_Keys.
   procedure Count_Key (Key : Value; Counts : in out Key_Counts; Array_Keys : in out Natural)
   with Global => null
   is
      Log : Natural;
   begin
      if Key.Kind = Integer_Value
        and then Integer_Of (Key) in 1 .. Maximum_Array_Size
      then
         Log := Ceiling_Log_2 (Positive (Integer_Of (Key)));
         if Log <= Maximum_Array_Bits and then Counts (Log) < Natural'Last then
            Counts (Log) := Counts (Log) + 1;
         end if;
         if Array_Keys < Natural'Last then
            Array_Keys := Array_Keys + 1;
         end if;
      end if;
   end Count_Key;

   --  [puc ltable.c:computesizes] The size of the array part: the largest power of two N such
   --  that more than half of 1 .. N are keys. Array_Keys becomes the number of keys that go
   --  to it.
   procedure Compute_Sizes
     (Counts : Key_Counts; Array_Keys : in out Natural; Optimal : out Natural)
   with Global => null, Post => Optimal <= Maximum_Array_Size and then Array_Keys <= Array_Keys'Old
   is
      Power : Natural := 1;
      Below : Natural := 0;
      Keys  : Natural := 0;
   begin
      Optimal := 0;
      for Bits in Key_Counts'Range loop
         exit when Array_Keys <= Power / 2;
         if Below <= Natural'Last - Counts (Bits) then
            Below := Below + Counts (Bits);
         end if;
         if Below > Power / 2 and then Below <= Array_Keys then
            Optimal := Power;
            Keys := Below;
         end if;
         exit when Power > Maximum_Array_Size / 2;
         pragma Loop_Invariant (Power <= Maximum_Array_Size / 2);
         pragma Loop_Invariant (Optimal <= Maximum_Array_Size);
         pragma Loop_Invariant (Keys <= Array_Keys);
         Power := Power * 2;
      end loop;
      Array_Keys := Keys;
   end Compute_Sizes;

   --  [puc ltable.c:rehash] Resizes the table for its keys and Key: the array part as
   --  Compute_Sizes finds it, the hash part for the other keys. Success is False, and the
   --  table unchanged, when Budget cannot pay.
   procedure Rehash
     (T : in out Table; Budget : in out Memory_Budget; Key : Value; Success : out Boolean)
   with
     Global => null,
     Pre    => Is_Valid (T),
     Post   =>
       Is_Valid (T)
       and then Seed (T) = Seed (T)'Old
       and then Limit (Budget) = Limit (Budget)'Old
       and then Model (T) = Model (T)'Old
       and then Entries_From (Entries (T), Entries (T)'Old, Nil, Nil)
       and then (if Success then T.Items /= null and then No_Dead (T.Nodes.all))
   is
      Counts     : Key_Counts := [others => 0];
      Array_Keys : Natural := 0;
      Total      : Natural := 1;
      Optimal    : Natural;
   begin
      if T.Items /= null then
         for I in T.Items'Range loop
            if T.Items (I) /= Nil then
               Count_Key (Integer_Value_Of (Integer_64 (I)), Counts, Array_Keys);
               if Total < Natural'Last then
                  Total := Total + 1;
               end if;
            end if;
         end loop;
         for J in T.Nodes'Range loop
            if T.Nodes (J).State = Used_Node then
               Count_Key (T.Nodes (J).Key, Counts, Array_Keys);
               if Total < Natural'Last then
                  Total := Total + 1;
               end if;
            end if;
         end loop;
      end if;
      Count_Key (Key, Counts, Array_Keys);
      Compute_Sizes (Counts, Array_Keys, Optimal);
      if Array_Keys > Total or else Total - Array_Keys > Maximum_Capacity / 2 then
         Success := False;
         return;
      end if;
      Resize_Parts (T, Budget, Optimal, Total - Array_Keys, Success);
   end Rehash;

   --  The hash part has room for one more key below three quarters of its nodes.
   function Has_Room (T : Table) return Boolean
   is (T.Nodes /= null and then T.Nodes'Length >= 4 and then T.Filled < T.Nodes'Length / 4 * 3);

   --  Puts new key Key (absent, not in the array part) with Item in the first node of its
   --  probe sequence that is not used. Placed is False, and the table unchanged, when every
   --  node is used.
   procedure Insert_New
     (T : in out Table; Key, Item : Value; Placed : out Boolean)
   with
     Global => null,
     Pre    =>
       Is_Valid (T)
       and then T.Items /= null
       and then Is_Key (Key)
       and then Is_Canonical (Key)
       and then not In_Array (T.Items.all, Key)
       and then Item /= Nil
       and then Is_Canonical (Item)
       and then not Value_Maps.Has_Key (Model (T), Key)
       and then (for all I in T.Nodes'Range =>
                   T.Nodes (I).State = Empty_Node or else T.Nodes (I).Key /= Key),
     Post   =>
       Is_Valid (T)
       and then Seed (T) = Seed (T)'Old
       and then (if Placed then Stored (Model (T), Model (T)'Old, Key, Item)
                 else Model (T) = Model (T)'Old)
       and then Entries_From (Entries (T), Entries (T)'Old, Key, Item)
   is
      Hash  : constant Unsigned_64 := Key_Hash (T.Seed, Key);
      Start : constant Natural := Home (T.Nodes'Length, Hash);
      Place : Natural := 0;
      Found : Integer := -1;
   begin
      Placed := False;
      if T.Nodes'Length = 0 then
         return;
      end if;
      for Step in 0 .. T.Nodes'Length - 1 loop
         Place := Step_At (T.Nodes'Length, Start, Step);
         if T.Nodes (Place).State /= Used_Node then
            Found := Step;
            exit;
         end if;
         pragma Loop_Invariant
           (for all Earlier in 0 .. Step =>
              T.Nodes (Step_At (T.Nodes'Length, Start, Earlier)).State = Used_Node);
      end loop;
      if Found < 0 then
         return;
      end if;
      if T.Nodes (Place).State = Empty_Node and then T.Filled < Natural'Last then
         T.Filled := T.Filled + 1;
      end if;
      declare
         Before : constant Node_Array := T.Nodes.all with Ghost;
      begin
         T.Nodes (Place) := (State => Used_Node, Key => Key, Hash => Hash, Item => Item);
         Lemma_Insert (T.Items.all, Before, T.Nodes.all, T.Seed, Place, Found, Key, Item);
         Lemma_Entries (T.Items.all, Before, T.Items.all, T.Nodes.all, Key, Item);
      end;
      Placed := True;
   end Insert_New;

   procedure Set
     (T      : in out Table;
      Budget : in out Memory_Budget;
      Key    : Value;
      Item   : Value;
      Status : out Set_Status)
   is
      K        : constant Value := Key_Of (Key);
      Initial  : constant Value_Sequences.Sequence := Entries (T) with Ghost;
      Position : Integer;
      Placed   : Boolean;
      Success  : Boolean;
   begin
      if K = Nil then
         Status := Invalid_Key;
         return;
      end if;
      Status := Done;
      if T.Items /= null then
         if In_Array (T.Items.all, K) then
            declare
               Before : constant Value_Array := T.Items.all with Ghost;
               Index  : constant Positive := Index_Of (T.Items.all, K);
            begin
               Lemma_Integer_Value (K);
               T.Items (Index) := Item;
               Lemma_Store_Item (Before, T.Items.all, T.Nodes.all, T.Seed, Index, Item);
               Lemma_Entries (Before, T.Nodes.all, T.Items.all, T.Nodes.all, K, Item);
            end;
            return;
         end if;
         Lemma_Findable (T.Items.all, T.Nodes.all, T.Seed);
         Position := Find (T.Nodes.all, T.Seed, K);
         if Position >= 0 then
            declare
               Before : constant Node_Array := T.Nodes.all with Ghost;
            begin
               T.Nodes (Position) :=
                 (State => (if Item = Nil then Dead_Node else Used_Node),
                  Key   => T.Nodes (Position).Key,
                  Hash  => T.Nodes (Position).Hash,
                  Item  => Item);
               Lemma_Store_Node (T.Items.all, Before, T.Nodes.all, T.Seed, Position, Item);
               Lemma_Entries (T.Items.all, Before, T.Items.all, T.Nodes.all, K, Item);
            end;
            return;
         end if;
      end if;
      if Item = Nil then
         --  Removing a key the table does not have.
         return;
      end if;
      pragma Assert (not Value_Maps.Has_Key (Model (T), K));
      if T.Items = null or else not Has_Room (T) then
         Rehash (T, Budget, K, Success);
         if not Success then
            Status := Out_Of_Memory;
            return;
         end if;
         if In_Array (T.Items.all, K) then
            declare
               Middle : constant Value_Sequences.Sequence := Entries (T) with Ghost;
               Before : constant Value_Array := T.Items.all with Ghost;
               Index  : constant Positive := Index_Of (T.Items.all, K);
            begin
               Lemma_Integer_Value (K);
               T.Items (Index) := Item;
               Lemma_Store_Item (Before, T.Items.all, T.Nodes.all, T.Seed, Index, Item);
               Lemma_Entries (Before, T.Nodes.all, T.Items.all, T.Nodes.all, K, Item);
               Lemma_Entries_Chain (Initial, Middle, Entries (T), K, Item);
            end;
            return;
         end if;
         pragma Assert
           (for all I in T.Nodes'Range =>
              T.Nodes (I).State = Empty_Node or else T.Nodes (I).Key /= K);
      end if;
      declare
         Middle : constant Value_Sequences.Sequence := Entries (T) with Ghost;
      begin
         pragma Assert (Entries_From (Middle, Initial, Nil, Nil));
         Insert_New (T, K, Item, Placed);
         Lemma_Entries_Chain (Initial, Middle, Entries (T), K, Item);
      end;
      if not Placed then
         --  Not reached: the hash part has room after a rehash.
         Status := Out_Of_Memory;
      end if;
   end Set;

   procedure Next
     (T         : Table;
      Key       : Value;
      Next_Key  : out Value;
      Next_Item : out Value;
      Status    : out Next_Status)
   is
      K           : Value;
      First_Index : Positive := 1;
      First_Node  : Natural := 0;
      Position    : Integer;
   begin
      Next_Key := Nil;
      Next_Item := Nil;
      Status := Finished;
      if T.Items = null or else T.Nodes = null then
         if Key /= Nil then
            Status := Invalid_Key;
         end if;
         return;
      end if;
      pragma Assert (Model (T) = Model_Of (T.Items.all, T.Nodes.all, T.Seed));
      if Key /= Nil then
         K := Key_Of (Key);
         if K = Nil then
            Status := Invalid_Key;
            return;
         elsif In_Array (T.Items.all, K) then
            First_Index := Index_Of (T.Items.all, K) + 1;
         else
            Lemma_Findable (T.Items.all, T.Nodes.all, T.Seed);
            Position := Find (T.Nodes.all, T.Seed, K);
            if Position < 0 then
               Status := Invalid_Key;
               return;
            end if;
            First_Index := T.Items'Length + 1;
            First_Node := Position + 1;
         end if;
      end if;
      for Index in First_Index .. T.Items'Last loop
         if T.Items (Index) /= Nil then
            Next_Key := Integer_Value_Of (Integer_64 (Index));
            Next_Item := T.Items (Index);
            Status := Found;
            return;
         end if;
      end loop;
      for J in First_Node .. T.Nodes'Last loop
         if T.Nodes (J).State = Used_Node then
            Next_Key := T.Nodes (J).Key;
            Next_Item := T.Nodes (J).Item;
            Status := Found;
            return;
         end if;
      end loop;
   end Next;

   --  [puc ltable.c:hash_search] A border after Size, where t[Size + 1] is not nil (and
   --  t[Size] is not nil either, or Size is 0): doubling from Size until an absent key, then a
   --  binary search between the last present one and it.
   function Hash_Search (T : Table; Size : Natural) return Integer_64
   with
     Global => null,
     Pre    =>
       Is_Valid (T)
       and then (Size = 0
                 or else Value_Maps.Has_Key (Model (T), Integer_Value_Of (Integer_64 (Size))))
       and then Value_Maps.Has_Key (Model (T), Integer_Value_Of (Integer_64 (Size) + 1)),
     Post   =>
       Hash_Search'Result >= 1
       and then Value_Maps.Has_Key (Model (T), Integer_Value_Of (Hash_Search'Result))
       and then (Hash_Search'Result = Integer_64'Last
                 or else not Value_Maps.Has_Key
                               (Model (T), Integer_Value_Of (Hash_Search'Result + 1)))
   is
      Present : Integer_64 := Integer_64 (Size);
      Absent  : Integer_64;
      Middle  : Integer_64;
   begin
      if Present = 0 then
         Present := 1;
      end if;
      --  Present is present; double it until an absent key.
      Absent := Present;
      loop
         pragma Loop_Invariant
           (Absent >= 1 and then Value_Maps.Has_Key (Model (T), Integer_Value_Of (Absent)));
         pragma Loop_Variant (Increases => Absent);
         Present := Absent;
         if Absent <= Integer_64'Last / 2 then
            Absent := Absent * 2;
         else
            Absent := Integer_64'Last;
            if Get (T, Integer_Value_Of (Absent)) /= Nil then
               --  A border at the largest integer.
               return Integer_64'Last;
            end if;
            exit;
         end if;
         exit when Get (T, Integer_Value_Of (Absent)) = Nil;
      end loop;
      --  Binary search: Present is present, Absent is not.
      pragma Assert
        (Present >= 1 and then Absent > Present
         and then Value_Maps.Has_Key (Model (T), Integer_Value_Of (Present))
         and then not Value_Maps.Has_Key (Model (T), Integer_Value_Of (Absent)));
      while Absent - Present > 1 loop
         pragma Loop_Variant (Decreases => Absent - Present);
         pragma Loop_Invariant
           (Present >= 1 and then Absent > Present
            and then Value_Maps.Has_Key (Model (T), Integer_Value_Of (Present))
            and then not Value_Maps.Has_Key (Model (T), Integer_Value_Of (Absent)));
         Middle := Present + (Absent - Present) / 2;
         if Get (T, Integer_Value_Of (Middle)) = Nil then
            Absent := Middle;
         else
            Present := Middle;
         end if;
      end loop;
      pragma Assert (Absent = Present + 1);
      return Present;
   end Hash_Search;

   function Length (T : Table) return Integer_64 is
      Size    : Natural;
      Present : Natural := 0;
      Absent  : Natural;
      Middle  : Natural;
   begin
      if T.Items = null or else T.Nodes = null then
         return 0;
      end if;
      pragma Assert (Model (T) = Model_Of (T.Items.all, T.Nodes.all, T.Seed));
      Size := T.Items'Length;
      if Size > 0 and then T.Items (Size) = Nil then
         --  A border in the array part.
         if Size >= 2 and then T.Items (Size - 1) /= Nil then
            pragma Assert (Integer_64 (Size - 1) + 1 = Integer_64 (Size));
            pragma Assert
              (not Value_Maps.Has_Key (Model (T), Integer_Value_Of (Integer_64 (Size))));
            return Integer_64 (Size - 1);
         end if;
         --  [puc ltable.c:binsearch] Present is 0 or present, Absent is absent.
         Absent := Size;
         while Absent - Present > 1 loop
            pragma Loop_Variant (Decreases => Absent - Present);
            pragma Loop_Invariant
              (Present < Absent and then Absent <= Size
               and then (Present = 0 or else T.Items (Present) /= Nil)
               and then T.Items (Absent) = Nil);
            Middle := Present + (Absent - Present) / 2;
            if T.Items (Middle) = Nil then
               Absent := Middle;
            else
               Present := Middle;
            end if;
         end loop;
         pragma Assert (Integer_64 (Present) + 1 = Integer_64 (Absent));
         pragma Assert
           (not Value_Maps.Has_Key (Model (T), Integer_Value_Of (Integer_64 (Absent))));
         pragma Assert
           (Present = 0
            or else Value_Maps.Has_Key (Model (T), Integer_Value_Of (Integer_64 (Present))));
         return Integer_64 (Present);
      end if;
      --  Size is 0 or present.
      pragma Assert
        (Size = 0 or else Value_Maps.Has_Key (Model (T), Integer_Value_Of (Integer_64 (Size))));
      if Get (T, Integer_Value_Of (Integer_64 (Size) + 1)) = Nil then
         pragma Assert
           (not Value_Maps.Has_Key (Model (T), Integer_Value_Of (Integer_64 (Size) + 1)));
         return Integer_64 (Size);
      end if;
      return Hash_Search (T, Size);
   end Length;

   function Longest_Probe (T : Table) return Natural is
      Longest : Natural := 0;
      Probe   : Natural;
   begin
      if T.Nodes = null or else T.Nodes'Length > Maximum_Capacity then
         return 0;
      end if;
      for J in T.Nodes'Range loop
         if T.Nodes (J).State /= Empty_Node then
            Probe := Distance (T.Nodes'Length, Home (T.Nodes'Length, T.Nodes (J).Hash),
                               J - T.Nodes'First);
            if Probe > Longest then
               Longest := Probe;
            end if;
         end if;
      end loop;
      return Longest;
   end Longest_Probe;

   procedure Clear (T : in out Table; Budget : in out Memory_Budget) is
   begin
      if T.Items /= null then
         Release (Budget, Item_Bytes * Byte_Count (T.Items'Length));
      end if;
      if T.Nodes /= null then
         Release (Budget, Node_Bytes * Byte_Count (T.Nodes'Length));
      end if;
      Free_Items (T.Items);
      Free_Nodes (T.Nodes);
      T.Filled := 0;
   end Clear;

end Pyro.Tables;
