--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  The rich report of a diagnostic: its place twice, the quoted line with a pointer, what, why
--  or the one fix, and "because" links (DESIGN.md, Diagnostics).

package Pyro.Diagnostics.Rendering with SPARK_Mode => On, Always_Terminates is

   --  Where a span is, for people and for tools.
   type Place is record
      Line        : Line_Number := 1;
      --  The bytes of the line, without its line break (Last = First - 1 when empty).
      Line_First  : Source_Position := 1;
      Line_Last   : Span_End := 0;
      --  Bytes from the start of the line, from 1.
      Byte_Column : Positive := 1;
      --  Grapheme clusters (bytes, on a line that is not UTF-8) before the span, plus 1.
      Column      : Positive := 1;
      --  Grapheme clusters (or bytes) the span covers on its line, at least 1.
      Width       : Positive := 1;
   end record;

   --  The place of Where in Source.
   function Locate (Source : Sources.Source; Where : Span) return Place
   with
     Global => null,
     Pre    => Natural (Where.First) <= Source.Length + 1,
     Post   =>
       Natural (Locate'Result.Line_First) <= Source.Length + 1
       and then Natural (Locate'Result.Line_Last) <= Source.Length
       and then Locate'Result.Line_Last >= Locate'Result.Line_First - 1;

   --  Appends the rich report of Item, ending with a line break. File is the file name to
   --  show in places.
   procedure Append_Rich_Message
     (Output : in out Character_Arrays.Growable_Array;
      Budget : in out Memory_Budget;
      Item   : Diagnostic;
      Table  : Symbol_Table;
      Source : Sources.Source;
      File   : String)
   with
     Global => null,
     Pre    =>
       Is_Valid (Table)
       and then Names_Exist (Item, Table)
       and then File'Length <= Sources.Maximum_Name_Length,
     Post   => Limit (Budget) = Limit (Budget)'Old;

end Pyro.Diagnostics.Rendering;
