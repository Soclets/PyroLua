--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  Conversion of Lua numerals (as the lexer reads them) to integers and floats.

with Interfaces;
with Pyro.Floats;

package Pyro.Numbers with SPARK_Mode => On, Always_Terminates is

   --  The value of a numeral: a Lua integer or a float.
   type Numeral_Value is record
      Is_Integer    : Boolean := True;
      Integer_Value : Interfaces.Integer_64 := 0;
      Float_Bits    : Pyro.Floats.Float_Bits := 0;
   end record;

   --  True when Text is a decimal float numeral as strtod reads it, unsigned: digits with an
   --  optional fraction (at least one digit in all), then an optional exponent ('e' or 'E', an
   --  optional sign, and at least one digit).
   function Is_Decimal_Numeral (Text : String) return Boolean
   with Global => null, Pre => Text'First = 1 and then Text'Last < Positive'Last;

   --  [puc lobject.c:luaO_str2num] Converts a numeral read by the lexer. Decimal integers that
   --  do not fit 64 bits become floats; hexadecimal integers wrap modulo 2^64; hexadecimal
   --  floats are rounded to nearest, ties to even. Valid is False for a malformed numeral.
   procedure Convert (Text : String; Value : out Numeral_Value; Valid : out Boolean)
   with Global => null, Pre => Text'First = 1 and then Text'Length in 1 .. 2 ** 30;

   --  [puc lobject.c:luaO_str2num] The number a string holds, as the VM reads one where Lua
   --  converts strings to numbers (for loops, and later tonumber and string arithmetic): a
   --  numeral with optional spaces around it and an optional sign. Valid is False when the
   --  string holds nothing else.
   procedure String_To_Number (Text : String; Value : out Numeral_Value; Valid : out Boolean)
   with Global => null, Pre => Text'First = 1 and then Text'Length <= 2 ** 30;

end Pyro.Numbers;
