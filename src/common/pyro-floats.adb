--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  IEEE 754 binary64 operations on raw bits; the body is trusted (see docs/PROOFS.md).

with Interfaces.C;

--  [trusted] IEEE 754 conversions and arithmetic outside SPARK's finite-float model, done by
--  the C library as luac does (docs/PROOFS.md).
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

   function Arithmetic (Kind : Operation; Left, Right : Float_Bits) return Float_Bits is
      function Compute (Kind : Interfaces.C.int; Left, Right : Float_Bits) return Float_Bits
      with Import, Convention => C, External_Name => "pyro_float_arithmetic";
   begin
      return Compute (Operation'Pos (Kind), Left, Right);
   end Arithmetic;

   function From_Integer (Value : Interfaces.Integer_64) return Float_Bits is
      function Convert (Value : Interfaces.Integer_64) return Float_Bits
      with Import, Convention => C, External_Name => "pyro_integer_to_float";
   begin
      return Convert (Value);
   end From_Integer;

   procedure To_Integer
     (Value : Float_Bits; Result : out Interfaces.Integer_64; Success : out Boolean)
   is
      function Convert
        (Value : Float_Bits; Result : access Interfaces.Integer_64) return Interfaces.C.int
      with Import, Convention => C, External_Name => "pyro_float_to_integer";
      Converted : aliased Interfaces.Integer_64 := 0;
   begin
      Success := Convert (Value, Converted'Access) = 1;
      Result := Converted;
   end To_Integer;

   function Is_NaN (Value : Float_Bits) return Boolean is
      use type Interfaces.Unsigned_64;
   begin
      return (Value and 16#7FF0_0000_0000_0000#) = 16#7FF0_0000_0000_0000#
        and then (Value and 16#000F_FFFF_FFFF_FFFF#) /= 0;
   end Is_NaN;

   function Is_Zero (Value : Float_Bits) return Boolean is
      use type Interfaces.Unsigned_64;
   begin
      return (Value and 16#7FFF_FFFF_FFFF_FFFF#) = 0;
   end Is_Zero;

end Pyro.Floats;
