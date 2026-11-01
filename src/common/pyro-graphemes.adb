--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  Grapheme clusters (Unicode UAX #29, extended clusters) and UTF-8 decoding, for the columns
--  and pointers of diagnostics.

package body Pyro.Graphemes with SPARK_Mode => On is

   Replacement : constant Code_Point := 16#FFFD#;

   function Decode (Text : String; Position : Positive) return Decoded is
      Invalid : constant Decoded := (Point => Replacement, Length => 1, Valid => False);
      Lead    : constant Natural := Character'Pos (Text (Position));
      Value   : Natural;
      Need    : Natural;
      Least   : Natural;
   begin
      if Lead < 16#80# then
         return (Point => Code_Point (Lead), Length => 1, Valid => True);
      elsif Lead in 16#C2# .. 16#DF# then
         Need := 1;
         Value := Lead - 16#C0#;
         Least := 16#80#;
      elsif Lead in 16#E0# .. 16#EF# then
         Need := 2;
         Value := Lead - 16#E0#;
         Least := 16#800#;
      elsif Lead in 16#F0# .. 16#F4# then
         Need := 3;
         Value := Lead - 16#F0#;
         Least := 16#1_0000#;
      else
         return Invalid;
      end if;
      if Text'Last - Position < Need then
         return Invalid;
      end if;
      for Offset in 1 .. Need loop
         pragma Loop_Invariant (Value < 2 ** (5 + 6 * (Offset - 1)));
         declare
            Byte : constant Natural := Character'Pos (Text (Position + Offset));
         begin
            if Byte not in 16#80# .. 16#BF# then
               return Invalid;
            end if;
            Value := Value * 64 + (Byte - 16#80#);
         end;
      end loop;
      if Value < Least or else Value > 16#10_FFFF# or else Value in 16#D800# .. 16#DFFF# then
         return Invalid;
      end if;
      return (Point => Code_Point (Value), Length => Need + 1, Valid => True);
   end Decode;

   function Is_Valid_UTF_8 (Text : String) return Boolean is
      Position : Positive;
      Sequence : Decoded;
   begin
      if Text'Length = 0 then
         return True;
      end if;
      Position := Text'First;
      loop
         pragma Loop_Invariant (Position in Text'Range);
         pragma Loop_Variant (Increases => Position);
         Sequence := Decode (Text, Position);
         if not Sequence.Valid then
            return False;
         end if;
         exit when Text'Last - Position < Sequence.Length;
         Position := Position + Sequence.Length;
      end loop;
      return True;
   end Is_Valid_UTF_8;

   function Break_Of (Point : Code_Point) return Break_Property is
      Low  : Positive := Breaks'First;
      High : Natural := Breaks'Last;
   begin
      while Low <= High loop
         pragma Loop_Invariant (Low >= Breaks'First and then High <= Breaks'Last);
         pragma Loop_Variant (Decreases => High - Low);
         declare
            Middle : constant Positive := Low + (High - Low) / 2;
         begin
            if Point < Breaks (Middle).First then
               High := Middle - 1;
            elsif Point > Breaks (Middle).Last then
               Low := Middle + 1;
            else
               return Breaks (Middle).Property;
            end if;
         end;
      end loop;
      return Other;
   end Break_Of;

   function Is_Pictographic (Point : Code_Point) return Boolean is
      Low  : Positive := Pictographic'First;
      High : Natural := Pictographic'Last;
   begin
      while Low <= High loop
         pragma Loop_Invariant (Low >= Pictographic'First and then High <= Pictographic'Last);
         pragma Loop_Variant (Decreases => High - Low);
         declare
            Middle : constant Positive := Low + (High - Low) / 2;
         begin
            if Point < Pictographic (Middle).First then
               High := Middle - 1;
            elsif Point > Pictographic (Middle).Last then
               Low := Middle + 1;
            else
               return True;
            end if;
         end;
      end loop;
      return False;
   end Is_Pictographic;

   function Conjunct_Of (Point : Code_Point) return Conjunct_Property is
      Low  : Positive := Conjuncts'First;
      High : Natural := Conjuncts'Last;
   begin
      while Low <= High loop
         pragma Loop_Invariant (Low >= Conjuncts'First and then High <= Conjuncts'Last);
         pragma Loop_Variant (Decreases => High - Low);
         declare
            Middle : constant Positive := Low + (High - Low) / 2;
         begin
            if Point < Conjuncts (Middle).First then
               High := Middle - 1;
            elsif Point > Conjuncts (Middle).Last then
               Low := Middle + 1;
            else
               return Conjuncts (Middle).Property;
            end if;
         end;
      end loop;
      return None;
   end Conjunct_Of;

   --  What GB11 has seen: a pictograph, then Extend characters, then a ZWJ.
   type Pictograph_State is (Nothing, After_Pictograph, After_Joiner);

   --  What GB9c has seen (Unicode 18: "ConjunctLinker ConjunctExtender* x LinkingConsonant"):
   --  a Linker, then only InCB=Extend characters.
   type Conjunct_State is (Nothing, After_Linker);

   --  [UAX #29 GB3-GB999] True when there is no boundary between a character with break
   --  property Before and the character Next.
   function Joined
     (Before     : Break_Property;
      Next       : Code_Point;
      Pictograph : Pictograph_State;
      Conjunct   : Conjunct_State;
      Odd_Flags  : Boolean) return Boolean
   is
      After : constant Break_Property := Break_Of (Next);
   begin
      if Before = Carriage_Return and then After = Line_Feed then
         return True;
      elsif Before in Control | Carriage_Return | Line_Feed
        or else After in Control | Carriage_Return | Line_Feed
      then
         return False;
      elsif Before = Hangul_L and then After in Hangul_L | Hangul_V | Hangul_LV | Hangul_LVT then
         return True;
      elsif Before in Hangul_LV | Hangul_V and then After in Hangul_V | Hangul_T then
         return True;
      elsif Before in Hangul_LVT | Hangul_T and then After = Hangul_T then
         return True;
      elsif After in Extend | Zero_Width_Joiner | Spacing_Mark or else Before = Prepend then
         return True;
      elsif Conjunct = After_Linker and then Conjunct_Of (Next) = Consonant then
         return True;
      elsif Pictograph = After_Joiner and then Is_Pictographic (Next) then
         return True;
      elsif Before = Regional_Indicator and then After = Regional_Indicator then
         return Odd_Flags;
      else
         return False;
      end if;
   end Joined;

   function Cluster_Last (Text : String; From : Positive) return Positive is
      Sequence   : Decoded := Decode (Text, From);
      Point      : Code_Point := Sequence.Point;
      Before     : Break_Property;
      Pictograph : Pictograph_State := Nothing;
      Conjunct   : Conjunct_State := Nothing;
      Odd_Flags  : Boolean := False;
      Last       : Positive;
      Next       : Positive;

      --  Updates the states with the character Point that is now part of the cluster.
      procedure Take (Property : Break_Property)
      with Global => (Input => Point, In_Out => (Pictograph, Conjunct, Odd_Flags))
      is
         Joining : constant Conjunct_Property := Conjunct_Of (Point);
      begin
         if Is_Pictographic (Point) then
            Pictograph := After_Pictograph;
         elsif Pictograph = After_Pictograph and then Property = Extend then
            null;
         elsif Pictograph = After_Pictograph and then Property = Zero_Width_Joiner then
            Pictograph := After_Joiner;
         else
            Pictograph := Nothing;
         end if;
         if Joining = Linker then
            Conjunct := After_Linker;
         elsif Conjunct = After_Linker and then Joining = Conjunct_Extend then
            null;
         else
            Conjunct := Nothing;
         end if;
         Odd_Flags := Property = Regional_Indicator and then not Odd_Flags;
      end Take;
   begin
      Last := From + Sequence.Length - 1;
      Before := Break_Of (Point);
      Take (Before);
      while Last < Text'Last loop
         pragma Loop_Invariant (Last in From .. Text'Last - 1);
         pragma Loop_Variant (Increases => Last);
         Next := Last + 1;
         Sequence := Decode (Text, Next);
         Point := Sequence.Point;
         exit when not Joined (Before, Point, Pictograph, Conjunct, Odd_Flags);
         Before := Break_Of (Point);
         Take (Before);
         Last := Next + Sequence.Length - 1;
      end loop;
      return Last;
   end Cluster_Last;

end Pyro.Graphemes;
