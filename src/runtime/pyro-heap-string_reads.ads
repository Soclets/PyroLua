--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  Reading strings of the heap whole, rather than a byte at a time through String_Byte. A
--  child of the heap, so that the heap's own proofs do not carry it.

package Pyro.Heap.String_Reads with SPARK_Mode => On, Always_Terminates is

   --  The bytes of string S, copied at once.
   function String_Text (H : Heap; S : Object_Handle) return String
   with
     Global => null,
     Pre    => Is_Valid (H) and then Kind_Of (H, S) = String_Object,
     Post   =>
       String_Text'Result'First = 1
       and then String_Text'Result'Length = String_Length (H, S)
       and then String_Text'Result'Length <= Maximum_String_Length;

end Pyro.Heap.String_Reads;
