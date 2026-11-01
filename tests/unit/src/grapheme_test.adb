--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  Checks Pyro.Graphemes against Unicode's GraphemeBreakTest.txt (tests/unit/data), which
--  tools/generate-grapheme-tables fetches with the tables. Prints failures; exits with failure
--  if there are any.

with Ada.Command_Line;
with Ada.Strings.Fixed;
with Ada.Text_IO;
with Pyro.Grapheme_Tables;
with Pyro.Graphemes;

procedure Grapheme_Test is
   use Ada.Text_IO;

   File     : File_Type;
   Failures : Natural := 0;
   Lines    : Natural := 0;

   --  Encodes a code point as UTF-8; surrogates are encoded as their three bytes would be.
   function Encode (Point : Natural) return String is
      function Byte (Value : Natural) return Character is (Character'Val (Value));
   begin
      if Point < 16#80# then
         return [1 => Byte (Point)];
      elsif Point < 16#800# then
         return Byte (16#C0# + Point / 64) & Byte (16#80# + Point mod 64);
      elsif Point < 16#1_0000# then
         return Byte (16#E0# + Point / 4096) & Byte (16#80# + Point / 64 mod 64)
           & Byte (16#80# + Point mod 64);
      else
         return Byte (16#F0# + Point / 262144) & Byte (16#80# + Point / 4096 mod 64)
           & Byte (16#80# + Point / 64 mod 64) & Byte (16#80# + Point mod 64);
      end if;
   end Encode;

   procedure Check (Line : String) is
      Text      : String (1 .. 4 * Line'Length);
      Last      : Natural := 0;
      Expected  : String (1 .. 4 * Line'Length) := [others => ' '];
      Position  : Positive := Line'First;
      Has_Surrogate : Boolean := False;
   begin
      --  Expected (I) = '|' when a cluster ends at byte I of Text.
      while Position <= Line'Last loop
         case Line (Position) is
            when ' ' | ASCII.HT => Position := Position + 1;
            when others =>
               if Line (Position) = Character'Val (16#C3#) then
                  --  U+00F7 DIVISION SIGN (break) or U+00D7 MULTIPLICATION SIGN (no break).
                  if Line (Position + 1) = Character'Val (16#B7#) and then Last > 0 then
                     Expected (Last) := '|';
                  end if;
                  Position := Position + 2;
               else
                  declare
                     Stop  : Natural := Position;
                  begin
                     while Stop <= Line'Last and then Line (Stop) not in ' ' | ASCII.HT loop
                        Stop := Stop + 1;
                     end loop;
                     declare
                        Point : constant Natural :=
                          Natural'Value ("16#" & Line (Position .. Stop - 1) & "#");
                        Bytes : constant String := Encode (Point);
                     begin
                        Has_Surrogate := Has_Surrogate or else Point in 16#D800# .. 16#DFFF#;
                        Text (Last + 1 .. Last + Bytes'Length) := Bytes;
                        Last := Last + Bytes'Length;
                     end;
                     Position := Stop;
                  end;
               end if;
         end case;
      end loop;
      if Has_Surrogate then
         --  Not UTF-8; a source line with a surrogate counts bytes instead.
         return;
      end if;
      Lines := Lines + 1;
      declare
         Actual : String (1 .. Last) := [others => ' '];
         Start  : Positive := 1;
      begin
         while Start <= Last loop
            declare
               Cluster : constant Positive := Pyro.Graphemes.Cluster_Last (Text (1 .. Last), Start);
            begin
               Actual (Cluster) := '|';
               Start := Cluster + 1;
            end;
         end loop;
         if Actual /= Expected (1 .. Last) then
            Failures := Failures + 1;
            Put_Line ("FAIL: " & Line);
         end if;
      end;
   end Check;
begin
   Open (File, In_File, Ada.Command_Line.Argument (1));
   while not End_Of_File (File) loop
      declare
         Line    : constant String := Get_Line (File);
         Comment : constant Natural := Ada.Strings.Fixed.Index (Line, "#");
      begin
         if Comment /= 1 and then Line'Length > 0 then
            Check (if Comment = 0 then Line else Line (Line'First .. Comment - 1));
         end if;
      end;
   end loop;
   Close (File);
   Put_Line ("Unicode " & Pyro.Grapheme_Tables.Unicode_Version & ": "
             & Natural'Image (Lines) & " lines," & Natural'Image (Failures) & " failures");
   if Failures > 0 then
      Ada.Command_Line.Set_Exit_Status (Ada.Command_Line.Failure);
   end if;
end Grapheme_Test;
