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

end Pyro.Integer_Arithmetic;
