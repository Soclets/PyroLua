--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  String bytes and the keyed hash of strings and table keys.

package body Pyro.Strings with SPARK_Mode => On is

   --  [SipHash] The state of the hash: four 64-bit words.
   type State is record
      V0, V1, V2, V3 : Unsigned_64;
   end record;

   function Start (Key : Seed) return State
   is ((V0 => Key.K0 xor 16#736f_6d65_7073_6575#,
        V1 => Key.K1 xor 16#646f_7261_6e64_6f6d#,
        V2 => Key.K0 xor 16#6c79_6765_6e65_7261#,
        V3 => Key.K1 xor 16#7465_6462_7974_6573#));

   --  [SipHash] SipRound, Rounds times.
   procedure Round (S : in out State; Rounds : Positive)
   with Global => null, Pre => Rounds <= 8
   is
   begin
      for Count in 1 .. Rounds loop
         S.V0 := S.V0 + S.V1;
         S.V1 := Rotate_Left (S.V1, 13);
         S.V1 := S.V1 xor S.V0;
         S.V0 := Rotate_Left (S.V0, 32);
         S.V2 := S.V2 + S.V3;
         S.V3 := Rotate_Left (S.V3, 16);
         S.V3 := S.V3 xor S.V2;
         S.V0 := S.V0 + S.V3;
         S.V3 := Rotate_Left (S.V3, 21);
         S.V3 := S.V3 xor S.V0;
         S.V2 := S.V2 + S.V1;
         S.V1 := Rotate_Left (S.V1, 17);
         S.V1 := S.V1 xor S.V2;
         S.V2 := Rotate_Left (S.V2, 32);
      end loop;
   end Round;

   --  [SipHash] Compresses message word Word.
   procedure Compress (S : in out State; Word : Unsigned_64; Rounds : Positive)
   with Global => null, Pre => Rounds <= 8
   is
   begin
      S.V3 := S.V3 xor Word;
      Round (S, Rounds);
      S.V0 := S.V0 xor Word;
   end Compress;

   --  [SipHash] The hash, after the last word.
   function Finish (S : State; Rounds : Positive) return Unsigned_64
   with Global => null, Pre => Rounds <= 8
   is
      Final : State := S;
   begin
      Final.V2 := Final.V2 xor 16#FF#;
      Round (Final, Rounds);
      return Final.V0 xor Final.V1 xor Final.V2 xor Final.V3;
   end Finish;

   function Sip_Hash
     (Key                 : Seed;
      Data                : Byte_Array;
      Compression_Rounds  : Positive;
      Finalization_Rounds : Positive) return Unsigned_64
   is
      S         : State := Start (Key);
      Length    : constant Natural := Data'Length;
      Full      : constant Natural := Length / 8;
      Word      : Unsigned_64;
      Remaining : Natural;
   begin
      --  Little-endian words of eight bytes.
      for Index in 0 .. Full - 1 loop
         Word := 0;
         for Byte in reverse 0 .. 7 loop
            Word := Shift_Left (Word, 8)
              or Character'Pos (Data (Data'First + Byte_Position'Base (Index * 8 + Byte)));
         end loop;
         Compress (S, Word, Compression_Rounds);
      end loop;
      --  The last word: the remaining bytes, and the length modulo 256 in the top byte.
      Remaining := Length - Full * 8;
      Word := Shift_Left (Unsigned_64 (Length mod 256), 56);
      for Byte in reverse 0 .. Remaining - 1 loop
         Word := Word or Shift_Left
           (Unsigned_64 (Character'Pos (Data (Data'First + Byte_Position'Base (Full * 8 + Byte)))),
            8 * Byte);
      end loop;
      Compress (S, Word, Compression_Rounds);
      return Finish (S, Finalization_Rounds);
   end Sip_Hash;

   function Hash (Key : Seed; Data : Byte_Array) return Unsigned_64
   is (Sip_Hash (Key, Data, 1, 3));

   function Hash_Words (Key : Seed; First, Second : Unsigned_64) return Unsigned_64 is
      S : State := Start (Key);
   begin
      Compress (S, First, 1);
      Compress (S, Second, 1);
      --  The length, 16, in the top byte of the last word.
      Compress (S, Shift_Left (16, 56), 1);
      return Finish (S, 3);
   end Hash_Words;

end Pyro.Strings;
