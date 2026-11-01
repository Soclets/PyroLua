--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  Grapheme clusters (Unicode UAX #29, extended clusters) and UTF-8 decoding, for the columns
--  and pointers of diagnostics.

with Pyro.Grapheme_Tables; use Pyro.Grapheme_Tables;

package Pyro.Graphemes with SPARK_Mode => On, Always_Terminates is

   --  The longest UTF-8 sequence.
   subtype Sequence_Length is Positive range 1 .. 4;

   --  A decoded UTF-8 sequence.
   type Decoded is record
      Point  : Code_Point;
      Length : Sequence_Length;
      Valid  : Boolean;
   end record;

   --  Decodes the UTF-8 sequence at Text (Position). An invalid or truncated sequence gives
   --  U+FFFD, one byte long, with Valid False.
   function Decode (Text : String; Position : Positive) return Decoded
   with
     Global => null,
     Pre    => Position in Text'Range and then Text'Last < Positive'Last,
     Post   => Position + Decode'Result.Length - 1 <= Text'Last;

   --  True when Text is well-formed UTF-8 (no surrogates, no overlong forms, at most U+10FFFF).
   function Is_Valid_UTF_8 (Text : String) return Boolean
   with Global => null, Pre => Text'Last < Positive'Last;

   --  The Grapheme_Cluster_Break property of Point.
   function Break_Of (Point : Code_Point) return Break_Property
   with Global => null;

   --  The Extended_Pictographic property of Point.
   function Is_Pictographic (Point : Code_Point) return Boolean
   with Global => null;

   --  The Indic_Conjunct_Break property of Point.
   function Conjunct_Of (Point : Code_Point) return Conjunct_Property
   with Global => null;

   --  The last byte of the grapheme cluster that starts at Text (From).
   function Cluster_Last (Text : String; From : Positive) return Positive
   with
     Global => null,
     Pre    => From in Text'Range and then Text'Last < Positive'Last,
     Post   => Cluster_Last'Result in From .. Text'Last;

end Pyro.Graphemes;
