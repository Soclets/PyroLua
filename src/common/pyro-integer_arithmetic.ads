--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  Lua's integer arithmetic: 64-bit two's complement, wrapping around on overflow.

with Interfaces; use Interfaces;

package Pyro.Integer_Arithmetic with SPARK_Mode => On, Pure, Always_Terminates is

   --  Two's complement reinterpretations.
   function To_Unsigned (Value : Integer_64) return Unsigned_64
   is (if Value >= 0 then Unsigned_64 (Value)
       else Unsigned_64'Last - Unsigned_64 (-(Value + 1)));

   function To_Signed (Value : Unsigned_64) return Integer_64
   is (if Value <= Unsigned_64 (Integer_64'Last) then Integer_64 (Value)
       else -Integer_64 (Unsigned_64'Last - Value) - 1);

   --  [puc llimits.h:intop] The operations, wrapping around as Lua's do.
   function Add (Left, Right : Integer_64) return Integer_64
   is (To_Signed (To_Unsigned (Left) + To_Unsigned (Right)));

   function Subtract (Left, Right : Integer_64) return Integer_64
   is (To_Signed (To_Unsigned (Left) - To_Unsigned (Right)));

   function Multiply (Left, Right : Integer_64) return Integer_64
   is (To_Signed (To_Unsigned (Left) * To_Unsigned (Right)));

   function Negate (Value : Integer_64) return Integer_64
   is (To_Signed (0 - To_Unsigned (Value)));

   function Bitwise_And (Left, Right : Integer_64) return Integer_64
   is (To_Signed (To_Unsigned (Left) and To_Unsigned (Right)));

   function Bitwise_Or (Left, Right : Integer_64) return Integer_64
   is (To_Signed (To_Unsigned (Left) or To_Unsigned (Right)));

   function Bitwise_Exclusive_Or (Left, Right : Integer_64) return Integer_64
   is (To_Signed (To_Unsigned (Left) xor To_Unsigned (Right)));

   function Bitwise_Not (Value : Integer_64) return Integer_64
   is (To_Signed (not To_Unsigned (Value)));

   --  [puc lvm.c:luaV_shiftl] Value shifted left by Count bits, right when Count is negative;
   --  64 bits or more give 0.
   function Shift_Left (Value, Count : Integer_64) return Integer_64
   is (if Count <= -64 or else Count >= 64 then 0
       elsif Count < 0 then To_Signed (Shift_Right (To_Unsigned (Value), Natural (-Count)))
       else To_Signed (Interfaces.Shift_Left (To_Unsigned (Value), Natural (Count))));

   --  [puc lvm.c:luaV_idiv] Floor division; Right must not be 0.
   function Floor_Divide (Left, Right : Integer_64) return Integer_64
   with Pre => Right /= 0;

   --  [puc lvm.c:luaV_mod] The remainder of floor division, with the sign of Right; Right must
   --  not be 0.
   function Modulo (Left, Right : Integer_64) return Integer_64
   with Pre => Right /= 0;

end Pyro.Integer_Arithmetic;
