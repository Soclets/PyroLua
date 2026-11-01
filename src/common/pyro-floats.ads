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

end Pyro.Floats;
