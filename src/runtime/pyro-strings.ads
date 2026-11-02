--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  String bytes and the keyed hash of strings and table keys.

with Interfaces; use Interfaces;

package Pyro.Strings with SPARK_Mode => On, Pure, Always_Terminates is

   --  The longest string, in bytes.
   Maximum_String_Length : constant := 2 ** 30 - 1;

   --  The bytes of a string.
   type Byte_Array is array (Byte_Position range <>) of Character;

   --  The secret key of a state's hashes. A script that cannot know it cannot choose
   --  strings or table keys that collide.
   type Seed is record
      K0 : Unsigned_64 := 0;
      K1 : Unsigned_64 := 0;
   end record;

   --  SipHash-1-3 of Data under Key: the hash of strings (Pyro hashes every string, short or
   --  long, over all its bytes).
   function Hash (Key : Seed; Data : Byte_Array) return Unsigned_64
   with Global => null;

   --  SipHash-1-3 of the 16 bytes First (little-endian) then Second: the hash of a table key
   --  that is not a string's contents.
   function Hash_Words (Key : Seed; First, Second : Unsigned_64) return Unsigned_64
   with Global => null;

   --  SipHash-c-d of Data under Key, for testing against the reference vectors (published
   --  for SipHash-2-4).
   function Sip_Hash
     (Key                 : Seed;
      Data                : Byte_Array;
      Compression_Rounds  : Positive;
      Finalization_Rounds : Positive) return Unsigned_64
   with Global => null, Pre => Compression_Rounds <= 8 and then Finalization_Rounds <= 8;

end Pyro.Strings;
