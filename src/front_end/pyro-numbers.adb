--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  Conversion of Lua numerals (as the lexer reads them) to integers and floats.

with Pyro.Integer_Arithmetic;

package body Pyro.Numbers with SPARK_Mode => On is

   use Interfaces;

   function Is_Decimal_Digit (Byte : Character) return Boolean is (Byte in '0' .. '9');

   function Is_Hexadecimal_Digit (Byte : Character) return Boolean
   is (Byte in '0' .. '9' | 'a' .. 'f' | 'A' .. 'F');

   function Hexadecimal_Value (Byte : Character) return Unsigned_64
   is (case Byte is
         when '0' .. '9' => Character'Pos (Byte) - Character'Pos ('0'),
         when 'a' .. 'f' => Character'Pos (Byte) - Character'Pos ('a') + 10,
         when others     => Character'Pos (Byte) - Character'Pos ('A') + 10)
   with Pre => Is_Hexadecimal_Digit (Byte), Post => Hexadecimal_Value'Result < 16;

   function Is_Decimal_Numeral (Text : String) return Boolean is
      Position    : Positive := Text'First;
      Digits_Seen : Boolean := False;
   begin
      while Position <= Text'Last and then Is_Decimal_Digit (Text (Position)) loop
         pragma Loop_Invariant (Position >= Text'First);
         pragma Loop_Variant (Increases => Position);
         Digits_Seen := True;
         Position := Position + 1;
      end loop;
      if Position <= Text'Last and then Text (Position) = '.' then
         Position := Position + 1;
         while Position <= Text'Last and then Is_Decimal_Digit (Text (Position)) loop
            pragma Loop_Invariant (Position >= Text'First);
            pragma Loop_Variant (Increases => Position);
            Digits_Seen := True;
            Position := Position + 1;
         end loop;
      end if;
      if not Digits_Seen then
         return False;
      end if;
      if Position <= Text'Last and then Text (Position) in 'e' | 'E' then
         Position := Position + 1;
         if Position <= Text'Last and then Text (Position) in '+' | '-' then
            Position := Position + 1;
         end if;
         if Position > Text'Last or else not Is_Decimal_Digit (Text (Position)) then
            return False;
         end if;
         while Position <= Text'Last and then Is_Decimal_Digit (Text (Position)) loop
            pragma Loop_Invariant (Position >= Text'First);
            pragma Loop_Variant (Increases => Position);
            Position := Position + 1;
         end loop;
      end if;
      return Position > Text'Last;
   end Is_Decimal_Numeral;

   --  [puc lobject.c:l_str2int] A decimal integer that fits, or a hexadecimal integer
   --  (wrapping). Valid is False when Text is neither, or a decimal integer overflows.
   procedure Integer_Numeral (Text : String; Result : out Integer_64; Valid : out Boolean)
   with Pre => Text'First = 1 and then Text'Length in 1 .. 2 ** 30
   is
      Maximum_By_10    : constant Unsigned_64 := Unsigned_64 (Integer_64'Last / 10);
      Maximum_Last_Digit : constant Unsigned_64 := Unsigned_64 (Integer_64'Last mod 10);
      Accumulated      : Unsigned_64 := 0;
   begin
      Result := 0;
      Valid := False;
      if Text'Length >= 2 and then Text (1) = '0' and then Text (2) in 'x' | 'X' then
         if Text'Length = 2 then
            return;
         end if;
         for Position in 3 .. Text'Last loop
            if not Is_Hexadecimal_Digit (Text (Position)) then
               return;
            end if;
            Accumulated := Accumulated * 16 + Hexadecimal_Value (Text (Position));
         end loop;
      else
         for Position in Text'Range loop
            if not Is_Decimal_Digit (Text (Position)) then
               return;
            end if;
            declare
               Digit : constant Unsigned_64 :=
                 Character'Pos (Text (Position)) - Character'Pos ('0');
            begin
               if Accumulated >= Maximum_By_10
                 and then (Accumulated > Maximum_By_10 or else Digit > Maximum_Last_Digit)
               then
                  return;
               end if;
               Accumulated := Accumulated * 10 + Digit;
            end;
            pragma Loop_Invariant (Accumulated <= Unsigned_64 (Integer_64'Last));
         end loop;
      end if;
      if Accumulated > Unsigned_64 (Integer_64'Last) then
         --  Two's complement wrap-around of a hexadecimal integer.
         Result := -Integer_64 (not Accumulated) - 1;
      else
         Result := Integer_64 (Accumulated);
      end if;
      Valid := True;
   end Integer_Numeral;

   --  The number of significant bits of Value (0 for zero).
   function Bit_Length (Value : Unsigned_64) return Natural
   with Pre => Value < 2 ** 60, Post => Bit_Length'Result <= 60
   is
   begin
      for Bits in reverse 0 .. 59 loop
         if (Value and Shift_Left (Unsigned_64'(1), Bits)) /= 0 then
            return Bits + 1;
         end if;
      end loop;
      return 0;
   end Bit_Length;

   --  Value / 2^Shift rounded to nearest, ties to even; Sticky says Value was followed by
   --  nonzero bits that were already dropped.
   function Shift_Right_Rounded
     (Value : Unsigned_64; Shift : Natural; Sticky : Boolean) return Unsigned_64
   with
     Pre  => Shift in 1 .. 63,
     Post => Shift_Right_Rounded'Result <= Shift_Right (Value, Shift) + 1
             and then Shift_Right_Rounded'Result >= Shift_Right (Value, Shift)
   is
      Kept : constant Unsigned_64 := Shift_Right (Value, Shift);
      Rest : constant Unsigned_64 := Value and (Shift_Left (1, Shift) - 1);
      Half : constant Unsigned_64 := Shift_Left (1, Shift - 1);
   begin
      if Rest > Half or else (Rest = Half and then (Sticky or else (Kept and 1) = 1)) then
         return Kept + 1;
      else
         return Kept;
      end if;
   end Shift_Right_Rounded;

   Infinity_Bits : constant Unsigned_64 := 16#7FF0_0000_0000_0000#;

   --  Bits of Mantissa * 2^Exponent (Mantissa below 2^60, followed by dropped nonzero bits when
   --  Sticky), rounded to binary64 as strtod does.
   function Round_To_Float
     (Mantissa : Unsigned_64; Exponent : Integer_64; Sticky : Boolean) return Unsigned_64
   with Pre => Mantissa < 2 ** 60 and then Exponent in -(2 ** 40) .. 2 ** 40
   is
      Length      : constant Natural := Bit_Length (Mantissa);
      Unbiased    : Integer_64;
      Significand : Unsigned_64;
   begin
      if Mantissa = 0 then
         return 0;
      end if;
      Unbiased := Exponent + Integer_64 (Length) - 1;
      if Unbiased > 1023 then
         return Infinity_Bits;
      elsif Unbiased >= -1022 then
         --  A normal number: 53 significant bits.
         if Length <= 53 then
            Significand := Shift_Left (Mantissa, 53 - Length);
         else
            Significand := Shift_Right_Rounded (Mantissa, Length - 53, Sticky);
            if Significand = 2 ** 53 then
               Significand := 2 ** 52;
               Unbiased := Unbiased + 1;
               if Unbiased > 1023 then
                  return Infinity_Bits;
               end if;
            end if;
         end if;
         return Shift_Left (Unsigned_64 (Unbiased + 1023), 52) + (Significand - 2 ** 52);
      else
         --  A subnormal number (or zero): a multiple of 2^-1074.
         declare
            Scale : constant Integer_64 := Exponent + 1074;
         begin
            if Scale >= 0 then
               return Shift_Left (Mantissa, Natural (Scale));
            elsif Scale < -60 then
               return 0;
            else
               return Shift_Right_Rounded (Mantissa, Natural (-Scale), Sticky);
            end if;
         end;
      end if;
   end Round_To_Float;

   --  [puc lobject.c:l_str2d] A hexadecimal float, read as C99 strtod does.
   procedure Hexadecimal_Float (Text : String; Bits : out Unsigned_64; Valid : out Boolean)
   with
     Pre => Text'First = 1 and then Text'Length in 3 .. 2 ** 30
            and then Text (1) = '0' and then Text (2) in 'x' | 'X'
   is
      Mantissa  : Unsigned_64 := 0;
      Sticky    : Boolean := False;
      Exponent  : Integer_64 := 0;
      Any_Digit : Boolean := False;
      Position  : Positive := 3;

      --  Adds one hexadecimal digit of the integer part or (Fraction) of the fraction.
      procedure Add_Digit (Digit : Unsigned_64; Fraction : Boolean)
      with
        Pre  => Digit < 16 and then Mantissa < 2 ** 60
                and then Exponent in (-4) * Integer_64 (Position) .. 4 * Integer_64 (Position)
                and then Position <= Text'Last,
        Post => Mantissa < 2 ** 60
                and then Exponent in (-4) * Integer_64 (Position) - 4
                                     .. 4 * Integer_64 (Position) + 4
      is
      begin
         if Mantissa < 2 ** 56 then
            Mantissa := Mantissa * 16 + Digit;
            if Fraction then
               Exponent := Exponent - 4;
            end if;
         else
            if Digit /= 0 then
               Sticky := True;
            end if;
            if not Fraction then
               Exponent := Exponent + 4;
            end if;
         end if;
      end Add_Digit;
   begin
      Bits := 0;
      Valid := False;
      while Position <= Text'Last and then Is_Hexadecimal_Digit (Text (Position)) loop
         pragma Loop_Invariant (Mantissa < 2 ** 60);
         pragma Loop_Invariant
           (Exponent in (-4) * Integer_64 (Position) .. 4 * Integer_64 (Position));
         pragma Loop_Variant (Increases => Position);
         Add_Digit (Hexadecimal_Value (Text (Position)), Fraction => False);
         Any_Digit := True;
         Position := Position + 1;
      end loop;
      if Position <= Text'Last and then Text (Position) = '.' then
         Position := Position + 1;
         while Position <= Text'Last and then Is_Hexadecimal_Digit (Text (Position)) loop
            pragma Loop_Invariant (Mantissa < 2 ** 60);
            pragma Loop_Invariant
              (Exponent in (-4) * Integer_64 (Position) .. 4 * Integer_64 (Position));
            pragma Loop_Variant (Increases => Position);
            Add_Digit (Hexadecimal_Value (Text (Position)), Fraction => True);
            Any_Digit := True;
            Position := Position + 1;
         end loop;
      end if;
      if not Any_Digit then
         return;
      end if;
      if Position <= Text'Last and then Text (Position) in 'p' | 'P' then
         Position := Position + 1;
         declare
            Negative : Boolean := False;
            Power    : Integer_64 := 0;
         begin
            if Position <= Text'Last and then Text (Position) in '+' | '-' then
               Negative := Text (Position) = '-';
               Position := Position + 1;
            end if;
            if Position > Text'Last or else not Is_Decimal_Digit (Text (Position)) then
               return;
            end if;
            while Position <= Text'Last and then Is_Decimal_Digit (Text (Position)) loop
               pragma Loop_Invariant (Power in 0 .. 2 ** 30);
               pragma Loop_Variant (Increases => Position);
               --  Saturate: any exponent this large already gives zero or infinity.
               Power := Integer_64'Min
                 (2 ** 30,
                  Power * 10 + Integer_64 (Character'Pos (Text (Position)) - Character'Pos ('0')));
               Position := Position + 1;
            end loop;
            Exponent := (if Negative then Exponent - Power else Exponent + Power);
         end;
      end if;
      if Position <= Text'Last then
         return;
      end if;
      Bits := Round_To_Float (Mantissa, Exponent, Sticky);
      Valid := True;
   end Hexadecimal_Float;

   procedure Convert (Text : String; Value : out Numeral_Value; Valid : out Boolean) is
      Integer_Result : Integer_64;
   begin
      Value := (Is_Integer => True, Integer_Value => 0, Float_Bits => 0);
      Integer_Numeral (Text, Integer_Result, Valid);
      if Valid then
         Value.Integer_Value := Integer_Result;
         return;
      end if;
      Value.Is_Integer := False;
      if Text'Length >= 3 and then Text (1) = '0' and then Text (2) in 'x' | 'X' then
         Hexadecimal_Float (Text, Value.Float_Bits, Valid);
      elsif Is_Decimal_Numeral (Text) then
         Pyro.Floats.Decimal_To_Bits (Text, Value.Float_Bits, Valid);
      else
         Valid := False;
      end if;
   end Convert;

   --  Text, numbered from 1.
   function From_One (Text : String) return String
   with Post => From_One'Result'First = 1 and then From_One'Result'Length = Text'Length
   is
      Result : String (1 .. Text'Length);
   begin
      for Index in Result'Range loop
         Result (Index) := Text (Text'First - 1 + Index);
      end loop;
      return Result;
   end From_One;

   procedure String_To_Number (Text : String; Value : out Numeral_Value; Valid : out Boolean) is
      --  [puc lctype.h:lisspace] The C locale's spaces.
      function Is_Space (Byte : Character) return Boolean
      is (Byte in ' ' | ASCII.HT | ASCII.LF | ASCII.VT | ASCII.FF | ASCII.CR);

      --  2 ** 63, which only a negative decimal integer reaches (l_str2int's maxlastd + neg).
      Minimum_Magnitude : constant String := "9223372036854775808";

      First    : Integer := Text'First;
      Last     : Integer := Text'Last;
      Negative : Boolean := False;
   begin
      Value := (Is_Integer => True, Integer_Value => 0, Float_Bits => 0);
      Valid := False;
      while First <= Last and then Is_Space (Text (First)) loop
         pragma Loop_Invariant (First in Text'First .. Last);
         pragma Loop_Variant (Increases => First);
         First := First + 1;
      end loop;
      while Last >= First and then Is_Space (Text (Last)) loop
         pragma Loop_Invariant (Last in First .. Text'Last);
         pragma Loop_Variant (Decreases => Last);
         Last := Last - 1;
      end loop;
      if First <= Last and then Text (First) in '-' | '+' then
         Negative := Text (First) = '-';
         First := First + 1;
      end if;
      if First > Last then
         return;
      end if;
      declare
         Numeral     : constant String := From_One (Text (First .. Last));
         Significant : Natural := 0;
      begin
         Convert (Numeral, Value, Valid);
         if not Valid or else not Negative then
            return;
         elsif Value.Is_Integer then
            Value.Integer_Value := Pyro.Integer_Arithmetic.Negate (Value.Integer_Value);
            return;
         end if;
         --  A decimal integer of magnitude 2 ** 63 is the minimum integer, not a float.
         for Index in Numeral'Range loop
            if Numeral (Index) /= '0' or else Significant > 0 then
               Significant := Significant + 1;
            end if;
            pragma Loop_Invariant (Significant <= Index);
         end loop;
         if (for all Byte of Numeral => Is_Decimal_Digit (Byte))
           and then Significant = Minimum_Magnitude'Length
           and then Numeral (Numeral'Last - Significant + 1 .. Numeral'Last) = Minimum_Magnitude
         then
            Value := (Is_Integer => True, Integer_Value => Integer_64'First, Float_Bits => 0);
         else
            Value.Float_Bits := Value.Float_Bits xor 16#8000_0000_0000_0000#;
         end if;
      end;
   end String_To_Number;

end Pyro.Numbers;
