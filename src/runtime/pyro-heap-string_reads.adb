--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  Reading strings of the heap whole.

package body Pyro.Heap.String_Reads with SPARK_Mode => On is

   --  [proof] A valid string slot owns its bytes, numbered from 1.
   procedure Lemma_String_Slot (Item : Slot)
   with
     Ghost,
     Global => null,
     Pre    => Slot_Valid (Item) and then Item.Kind = String_Object,
     Post   =>
       Item.Bytes /= null
       and then Item.Bytes'First = 1
       and then Item.Bytes'Last <= Maximum_String_Length
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Slot_Valid);
   begin
      null;
   end Lemma_String_Slot;

   function String_Text (H : Heap; S : Object_Handle) return String is
      P : constant Place := Place_Of (S);
   begin
      pragma Assert (Handle_Valid (H, S));
      Lemma_String_Slot (H.Chunks (P.Chunk) (P.Offset));
      return String (H.Chunks (P.Chunk) (P.Offset).Bytes.all);
   end String_Text;

end Pyro.Heap.String_Reads;
