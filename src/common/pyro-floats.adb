--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  IEEE 754 binary64 operations on raw bits; the body is trusted (see docs/PROOFS.md).

with Interfaces.C;

--  [trusted] IEEE 754 conversions outside SPARK's finite-float model (docs/PROOFS.md).
package body Pyro.Floats with SPARK_Mode => Off is

   use type Interfaces.C.int;

   procedure Decimal_To_Bits (Text : String; Bits : out Float_Bits; Success : out Boolean) is
      function Convert
        (Text : Interfaces.C.char_array; Bits : access Interfaces.Unsigned_64)
         return Interfaces.C.int
      with Import, Convention => C, External_Name => "pyro_decimal_to_bits";
      Result : aliased Interfaces.Unsigned_64 := 0;
   begin
      Success := Convert (Interfaces.C.To_C (Text), Result'Access) = 1;
      Bits := Result;
   end Decimal_To_Bits;

end Pyro.Floats;
