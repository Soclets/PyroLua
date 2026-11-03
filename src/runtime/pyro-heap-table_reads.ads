--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  Reading tables of the heap: the key after a key, a border, and the parts' sizes. A child
--  of the heap, so that the heap's own proofs do not carry these operations.

package Pyro.Heap.Table_Reads with SPARK_Mode => On, Always_Terminates is

   --  The key after Key in table T and its value (Pyro.Tables.Next).
   procedure Table_Next
     (H         : Heap;
      T         : Valid_Handle;
      Key       : Value;
      Next_Key  : out Value;
      Next_Item : out Value;
      Status    : out Pyro.Tables.Next_Status)
   with
     Global => null,
     Pre    => Is_Valid (H) and then Kind_Of (H, T) = Table_Object and then Is_Canonical (Key),
     Post   =>
       Is_Canonical (Next_Key)
       and then Is_Live (H, Next_Key)
       and then Is_Canonical (Next_Item)
       and then Is_Live (H, Next_Item);

   --  A border of table T (Pyro.Tables.Length).
   procedure Table_Length (H : Heap; T : Valid_Handle; Length : out Integer_64)
   with
     Global => null,
     Pre    => Is_Valid (H) and then Kind_Of (H, T) = Table_Object,
     Post   => Length >= 0;

   --  The sizes of table T's parts (Pyro.Tables.Array_Size and Hash_Room).
   procedure Table_Sizes
     (H : Heap; T : Valid_Handle; Array_Size : out Natural; Hash_Room : out Natural)
   with
     Global => null,
     Pre    => Is_Valid (H) and then Kind_Of (H, T) = Table_Object,
     Post   =>
       Array_Size <= Pyro.Tables.Maximum_Array_Size
       and then Hash_Room <= Pyro.Tables.Maximum_Capacity / 2;

end Pyro.Heap.Table_Reads;
