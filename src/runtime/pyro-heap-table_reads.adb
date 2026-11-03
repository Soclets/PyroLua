--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  Reading tables of the heap: the key after a key, a border, and the parts' sizes.

package body Pyro.Heap.Table_Reads with SPARK_Mode => On is

   --  [proof] The table a valid table slot owns is allocated and valid.
   procedure Lemma_Table_Slot (Item : Slot)
   with
     Ghost,
     Global => null,
     Pre    => Slot_Valid (Item) and then Item.Kind = Table_Object,
     Post   =>
       Item.Table /= null
       and then Pyro.Tables.Is_Valid (Item.Table.all)
       and then Refs_Valid (Item.Refs)
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Slot_Valid);
   begin
      null;
   end Lemma_Table_Slot;

   procedure Table_Next
     (H         : Heap;
      T         : Valid_Handle;
      Key       : Value;
      Next_Key  : out Value;
      Next_Item : out Value;
      Status    : out Pyro.Tables.Next_Status)
   is
      use type Pyro.Tables.Next_Status;
      P : constant Place := Place_Of (T);
   begin
      pragma Assert (Handle_Valid (H, T));
      Lemma_Table_Slot (H.Chunks (P.Chunk) (P.Offset));
      Lemma_Graph_Live (H);
      Pyro.Tables.Next
        (H.Chunks (P.Chunk) (P.Offset).Table.all, Key, Next_Key, Next_Item, Status);
      if Status = Pyro.Tables.Found then
         Pyro.Tables.Lemma_Model_In_Entries (H.Chunks (P.Chunk) (P.Offset).Table.all, Next_Key);
         pragma Assert (Graph_Sequences.Get (Graph (H), T) = Children (H, T));
      end if;
   end Table_Next;

   procedure Table_Length (H : Heap; T : Valid_Handle; Length : out Integer_64) is
      P : constant Place := Place_Of (T);
   begin
      pragma Assert (Handle_Valid (H, T));
      Lemma_Table_Slot (H.Chunks (P.Chunk) (P.Offset));
      Length := Pyro.Tables.Length (H.Chunks (P.Chunk) (P.Offset).Table.all);
   end Table_Length;

   procedure Table_Sizes
     (H : Heap; T : Valid_Handle; Array_Size : out Natural; Hash_Room : out Natural)
   is
      P : constant Place := Place_Of (T);
   begin
      pragma Assert (Handle_Valid (H, T));
      Lemma_Table_Slot (H.Chunks (P.Chunk) (P.Offset));
      Array_Size := Pyro.Tables.Array_Size (H.Chunks (P.Chunk) (P.Offset).Table.all);
      Hash_Room := Pyro.Tables.Hash_Room (H.Chunks (P.Chunk) (P.Offset).Table.all);
   end Table_Sizes;

end Pyro.Heap.Table_Reads;
