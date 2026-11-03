--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  IEEE 754 binary64 operations on raw bits; the body is trusted (see docs/PROOFS.md).

with Interfaces;

package Pyro.Floats with SPARK_Mode => On, Always_Terminates is

   --  A float, as the 64 bits of its IEEE 754 binary64 representation. SPARK assumes floating
   --  point values are finite, so Lua's floats (which may be infinite or NaN) are kept as bits.
   subtype Float_Bits is Interfaces.Unsigned_64;

   --  The correctly rounded value of the decimal numeral Text (round to nearest, ties to even;
   --  too large gives infinity, too small zero or a subnormal), as strtod gives in the C locale.
   --  Success is False when Text is not entirely a decimal numeral.
   procedure Decimal_To_Bits (Text : String; Bits : out Float_Bits; Success : out Boolean)
   with Global => null, Pre => Text'Length in 1 .. 2 ** 30;

   --  Lua's float arithmetic (llimits.h's luai_num* macros): +, -, *, / and unary minus in
   --  IEEE 754 binary64, ^ as C's pow, // as floor (a / b), and % as fmod corrected to take the
   --  sign of the divisor. Negate ignores Right.
   type Operation is
     (Add, Subtract, Multiply, Divide, Power, Floor_Divide, Modulo, Negate);

   --  [puc lobject.c:numarith] The result of Left Operation Right, computed as luac does.
   function Arithmetic (Kind : Operation; Left, Right : Float_Bits) return Float_Bits
   with Global => null;

   --  The float nearest to Value, as C's conversion from a 64-bit integer gives it.
   function From_Integer (Value : Interfaces.Integer_64) return Float_Bits
   with Global => null;

   --  [puc lvm.c:luaV_flttointeger] Value as an integer when it has an integral value in the
   --  range of a 64-bit integer (mode F2Ieq); Success is False otherwise.
   procedure To_Integer
     (Value : Float_Bits; Result : out Interfaces.Integer_64; Success : out Boolean)
   with Global => null;

   --  The comparisons of floats.
   type Comparison is (Equal, Less_Than, Less_Equal);

   --  [puc llimits.h:luai_numeq, luai_numlt, luai_numle] Left Kind Right, as C compares
   --  doubles: false when either is a NaN, and -0.0 equal to 0.0.
   function Compare (Kind : Comparison; Left, Right : Float_Bits) return Boolean
   with Global => null;

   --  True for a NaN.
   function Is_NaN (Value : Float_Bits) return Boolean
   with Global => null;

   --  True for +0.0 and -0.0.
   function Is_Zero (Value : Float_Bits) return Boolean
   with Global => null;

   --  The longest text Image gives: "%.14g" of a float is at most 21 characters
   --  ("-1.2345678901234e-308"), and ".0" may follow.
   Maximum_Image_Length : constant := 23;

   --  [puc lobject.c:tostringbuff] Value as Lua writes a float: C's "%.14g" (so "1e+15",
   --  "inf", "-inf", and "nan" or "-nan" as the C library writes them), followed by ".0" when
   --  that looks like an integer ("1.0", "-0.0").
   function Image (Value : Float_Bits) return String
   with
     Global => null,
     Post   => Image'Result'First = 1 and then Image'Result'Length in 1 .. Maximum_Image_Length;

end Pyro.Floats;
