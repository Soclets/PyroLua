--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  Lua's integer arithmetic: 64-bit two's complement, wrapping around on overflow.

package body Pyro.Integer_Arithmetic with SPARK_Mode => On is

   function Floor_Divide (Left, Right : Integer_64) return Integer_64 is
      Quotient : Integer_64;
   begin
      if Right = -1 then
         --  Avoids the overflow of Integer_64'First / -1.
         return Negate (Left);
      end if;
      Quotient := Left / Right;
      if (Left < 0) /= (Right < 0) and then Left rem Right /= 0 then
         Quotient := Quotient - 1;
      end if;
      return Quotient;
   end Floor_Divide;

   function Modulo (Left, Right : Integer_64) return Integer_64 is
      Remainder : Integer_64;
   begin
      if Right = -1 then
         return 0;
      end if;
      Remainder := Left rem Right;
      if Remainder /= 0 and then (Remainder < 0) /= (Right < 0) then
         Remainder := Remainder + Right;
      end if;
      return Remainder;
   end Modulo;

   --  Text, indexed from 1.
   function From_One (Text : String) return String
   with Post => From_One'Result'First = 1 and then From_One'Result'Length = Text'Length
   is
      Result : constant String (1 .. Text'Length) := Text;
   begin
      return Result;
   end From_One;

   function Image (Value : Integer_64) return String is
      Text      : String (1 .. Maximum_Image_Length) := [others => '0'];
      First     : Positive := Maximum_Image_Length;
      Magnitude : Unsigned_64 :=
        (if Value < 0 then 0 - To_Unsigned (Value) else To_Unsigned (Value));
   begin
      --  An integer's magnitude has at most 19 digits (2 ** 63 is 9223372036854775808), which
      --  leaves place 1 for the sign.
      loop
         pragma Loop_Invariant (First in 2 .. Maximum_Image_Length);
         pragma Loop_Variant (Decreases => First);
         Text (First) := Character'Val (Character'Pos ('0') + Natural (Magnitude mod 10));
         Magnitude := Magnitude / 10;
         exit when Magnitude = 0 or else First = 2;
         First := First - 1;
      end loop;
      if Value < 0 then
         First := First - 1;
         Text (First) := '-';
      end if;
      return From_One (Text (First .. Maximum_Image_Length));
   end Image;

end Pyro.Integer_Arithmetic;
