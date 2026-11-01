--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  The rich report of a diagnostic: its place twice, the quoted line with a pointer, what, why
--  or the one fix, and "because" links (DESIGN.md, Diagnostics).

with Pyro.Graphemes;

package body Pyro.Diagnostics.Rendering with SPARK_Mode => On is

   --  The longest piece of source quoted inside a sentence.
   Quote_Limit : constant := 40;

   function Is_Line_Break (Byte : Character) return Boolean
   is (Byte = ASCII.LF or else Byte = ASCII.CR);

   --  The span lies in the source (its end may be the end of the chunk).
   function Fits (Source : Sources.Source; Where : Span) return Boolean
   is (Natural (Where.First) <= Source.Length + 1);

   function Locate (Source : Sources.Source; Where : Span) return Place is
      Result   : Place;
      Position : Natural := 1;
      Lines    : Natural := 1;
      Start    : Positive := 1;
      Last     : Natural;
   begin
      --  The line's first byte: just after the previous line break.
      for Index in reverse 1 .. Natural (Where.First) - 1 loop
         if Is_Line_Break (Source.Text (Index)) then
            Start := Index + 1;
            exit;
         end if;
         pragma Loop_Invariant (Start = 1);
      end loop;
      --  [puc llex.c:inclinenumber] Lines before it, counting "\r\n" and "\n\r" once.
      while Position < Start loop
         pragma Loop_Invariant (Position >= 1 and then Lines <= Position);
         pragma Loop_Variant (Increases => Position);
         if Is_Line_Break (Source.Text (Position)) then
            if Position + 1 < Start
              and then Is_Line_Break (Source.Text (Position + 1))
              and then Source.Text (Position + 1) /= Source.Text (Position)
            then
               Position := Position + 1;
            end if;
            Lines := Lines + 1;
         end if;
         Position := Position + 1;
      end loop;
      Last := Start - 1;
      while Last < Source.Length and then not Is_Line_Break (Source.Text (Last + 1)) loop
         pragma Loop_Invariant (Last >= Start - 1);
         pragma Loop_Variant (Increases => Last);
         Last := Last + 1;
      end loop;
      Result.Line := Line_Number (Natural'Min (Lines, Maximum_Source_Length + 1));
      Result.Line_First := Source_Position (Start);
      Result.Line_Last := Source_Position'Base (Last);
      Result.Byte_Column := Natural (Where.First) - Start + 1;

      declare
         Span_Last : constant Natural :=
           Natural'Min (Natural'Max (Natural (Where.Last), Natural (Where.First)), Last);
      begin
         if Pyro.Graphemes.Is_Valid_UTF_8 (Source.Text (Start .. Last)) then
            --  Clusters entirely before the span, then the clusters it touches.
            declare
               Cluster : Positive := Start;
               Column  : Positive := 1;
               Width   : Natural := 0;
               Cluster_End : Positive;
            begin
               while Cluster <= Last loop
                  pragma Loop_Invariant (Cluster in Start .. Last and then Column <= Cluster);
                  pragma Loop_Variant (Increases => Cluster);
                  Cluster_End := Pyro.Graphemes.Cluster_Last (Source.Text (Start .. Last), Cluster);
                  exit when Cluster_End >= Natural (Where.First);
                  Column := Column + 1;
                  exit when Cluster_End = Last;
                  Cluster := Cluster_End + 1;
               end loop;
               Result.Column := Column;
               if Cluster <= Last and then Natural (Where.First) <= Last then
                  while Cluster <= Span_Last loop
                     pragma Loop_Invariant (Cluster in Start .. Last and then Width < Cluster);
                     pragma Loop_Variant (Increases => Cluster);
                     Cluster_End :=
                       Pyro.Graphemes.Cluster_Last (Source.Text (Start .. Last), Cluster);
                     Width := Width + 1;
                     exit when Cluster_End = Last;
                     Cluster := Cluster_End + 1;
                  end loop;
               end if;
               Result.Width := Natural'Max (Width, 1);
            end;
         else
            Result.Column := Result.Byte_Column;
            Result.Width := Natural'Max (Span_Last - Natural (Where.First) + 1, 1);
         end if;
      end;
      return Result;
   end Locate;

   --  Appends Count copies of Byte.
   procedure Append_Copies
     (Output : in out Character_Arrays.Growable_Array;
      Budget : in out Memory_Budget;
      Byte   : Character;
      Count  : Natural)
   with Post => Limit (Budget) = Limit (Budget)'Old
   is
   begin
      for Index in 1 .. Count loop
         pragma Loop_Invariant (Limit (Budget) = Limit (Budget)'Loop_Entry);
         Append (Output, Budget, [1 => Byte]);
      end loop;
   end Append_Copies;

   --  Appends "file:line:byte_column, line N column M".
   procedure Append_Place
     (Output : in out Character_Arrays.Growable_Array;
      Budget : in out Memory_Budget;
      File   : String;
      Where  : Place)
   with Pre => File'Length <= Sources.Maximum_Name_Length,
        Post => Limit (Budget) = Limit (Budget)'Old
   is
      Line : constant String := Image (Natural (Where.Line));
   begin
      Append (Output, Budget, File);
      Append (Output, Budget, ":" & Line & ":" & Image (Where.Byte_Column) & ", line " & Line
                              & " column " & Image (Where.Column));
   end Append_Place;

   --  Appends the quoted line, with its number in a margin of Margin digits, and the pointer.
   procedure Append_Quote
     (Output : in out Character_Arrays.Growable_Array;
      Budget : in out Memory_Budget;
      Source : Sources.Source;
      Where  : Place;
      Margin : Positive)
   with
     Pre  =>
       Margin <= 10
       and then Natural (Where.Line_First) <= Source.Length + 1
       and then Natural (Where.Line_Last) <= Source.Length,
     Post => Limit (Budget) = Limit (Budget)'Old
   is
      Number : constant String := Image (Natural (Where.Line));
   begin
      Append (Output, Budget, " ");
      Append_Copies (Output, Budget, ' ', Margin - Natural'Min (Number'Length, Margin));
      Append (Output, Budget, Number & " | ");
      for Index in Natural (Where.Line_First) .. Natural (Where.Line_Last) loop
         pragma Loop_Invariant (Limit (Budget) = Limit (Budget)'Loop_Entry);
         --  A tab is one cluster; showing it as one space keeps the pointer under its part.
         Append (Output, Budget,
                 [1 => (if Source.Text (Index) = ASCII.HT then ' ' else Source.Text (Index))]);
      end loop;
      Append (Output, Budget, [1 => ASCII.LF]);
      Append (Output, Budget, " ");
      Append_Copies (Output, Budget, ' ', Margin);
      Append (Output, Budget, " | ");
      Append_Copies (Output, Budget, ' ', Where.Column - 1);
      Append_Copies (Output, Budget, '^', Where.Width);
      Append (Output, Budget, [1 => ASCII.LF]);
   end Append_Quote;

   --  Appends the source bytes of Where in backquotes, cut at its line's end and at
   --  Quote_Limit bytes.
   procedure Append_Source_Text
     (Output : in out Character_Arrays.Growable_Array;
      Budget : in out Memory_Budget;
      Source : Sources.Source;
      Where  : Span)
   with Post => Limit (Budget) = Limit (Budget)'Old
   is
      Last : Natural := Natural'Min (Natural (Where.Last), Source.Length);
   begin
      Append (Output, Budget, "`");
      if Natural (Where.First) <= Last then
         for Index in Natural (Where.First) .. Last loop
            if Is_Line_Break (Source.Text (Index)) then
               Last := Index - 1;
               exit;
            end if;
            pragma Loop_Invariant (Last <= Source.Length);
         end loop;
         if Last >= Natural (Where.First) then
            Append (Output, Budget,
                    Source.Text (Natural (Where.First)
                                 .. Natural'Min (Last, Natural (Where.First) + Quote_Limit - 1)));
            if Last - Natural (Where.First) + 1 > Quote_Limit then
               Append (Output, Budget, "...");
            end if;
         end if;
      end if;
      Append (Output, Budget, "`");
   end Append_Source_Text;

   --  Appends how the found token reads in a sentence: its text in backquotes, or "the end of
   --  the chunk".
   procedure Append_Found
     (Output : in out Character_Arrays.Growable_Array;
      Budget : in out Memory_Budget;
      Item   : Diagnostic;
      Source : Sources.Source)
   with Post => Limit (Budget) = Limit (Budget)'Old
   is
   begin
      if Item.Found = End_Of_Stream then
         Append (Output, Budget, "the end of the chunk");
      elsif Item.Found = String_Literal then
         Append (Output, Budget, "a string");
      elsif Item.Found in Token_With_Text then
         Append_Source_Text (Output, Budget, Source, Item.Place);
      elsif Item.Found = Other_Byte then
         if Item.Found_Byte in ' ' .. '~' then
            Append (Output, Budget, "`" & Item.Found_Byte & "`");
         else
            Append (Output, Budget, "byte " & Image (Character'Pos (Item.Found_Byte)));
         end if;
      else
         Append (Output, Budget, "`" & Spelling (Item.Found) & "`");
      end if;
   end Append_Found;

   --  Appends a symbol in backquotes.
   procedure Append_Name
     (Output : in out Character_Arrays.Growable_Array;
      Budget : in out Memory_Budget;
      Table  : Symbol_Table;
      Symbol : Symbol_Index)
   with
     Pre  => Is_Valid (Table) and then Symbol <= Count (Table),
     Post => Limit (Budget) = Limit (Budget)'Old
   is
   begin
      Append (Output, Budget, "`");
      if Symbol /= No_Symbol then
         Append (Output, Budget, Text (Table, Symbol));
      end if;
      Append (Output, Budget, "`");
   end Append_Name;

   --  The manual section of the construct a token opens.
   function Section_Of (Opener : Token_Kind) return String
   is (case Opener is
         when Keyword_For => "3.3.5",
         when Keyword_Function => "3.4.11",
         when Left_Brace => "3.4.9",
         when Left_Parenthesis | Left_Bracket => "3.4",
         when others => "3.3.4");

   --  The error is at "!=", which Lua spells "~=".
   function Is_Not_Equal_Typo (Item : Diagnostic; Source : Sources.Source) return Boolean
   is (Item.What in Unexpected_Symbol | Token_Expected | Token_Expected_To_Close
       and then Item.Found = Other_Byte
       and then Item.Found_Byte = '!'
       and then Natural (Item.Place.First) < Source.Length
       and then Source.Text (Natural (Item.Place.First) + 1) = '=');

   --  Appends the "what:" (or "fix:") and "why:" lines.
   procedure Append_Explanation
     (Output : in out Character_Arrays.Growable_Array;
      Budget : in out Memory_Budget;
      Item   : Diagnostic;
      Table  : Symbol_Table;
      Source : Sources.Source)
   with
     Pre  => Is_Valid (Table) and then Names_Exist (Item, Table),
     Post => Limit (Budget) = Limit (Budget)'Old
   is
      Lexical : constant String := " (Lua 5.4 manual §3.1)";

      procedure What (Text : String) with Post => Limit (Budget) = Limit (Budget)'Old is
      begin
         Append (Output, Budget, " what: ");
         Append (Output, Budget, Text);
      end What;

      procedure Why (Text : String) with Post => Limit (Budget) = Limit (Budget)'Old is
      begin
         Append (Output, Budget, [1 => ASCII.LF] & " why:  ");
         Append (Output, Budget, Text);
         Append (Output, Budget, [1 => ASCII.LF]);
      end Why;

      procedure Place_Text with Post => Limit (Budget) = Limit (Budget)'Old is
      begin
         Append_Source_Text (Output, Budget, Source, Item.Place);
      end Place_Text;
   begin
      if Is_Not_Equal_Typo (Item, Source) then
         --  "!=" has exactly one fix in Lua.
         Append (Output, Budget, " fix:  `~=`");
         Why ("Lua's not-equal operator is `~=` (Lua 5.4 manual §3.4.4)");
         return;
      end if;
      case Item.What is
         when Malformed_Number =>
            What ("");
            Place_Text;
            Append (Output, Budget, " is not a valid number");
            Why ("a numeral is decimal or 0x-hexadecimal digits with an optional fraction and "
                 & "exponent, and no letter may touch it" & Lexical);
         when Unfinished_String =>
            What ("this string has no closing `");
            if Natural (Item.Place.First) <= Source.Length then
               Append (Output, Budget, [1 => Source.Text (Natural (Item.Place.First))]);
            end if;
            Append (Output, Budget, "`");
            Why ("a short string ends on the line where it starts" & Lexical);
         when Unfinished_Long_String | Unfinished_Long_Comment =>
            What ("this long " & (if Item.What = Unfinished_Long_String then "string"
                                  else "comment") & " has no closing `]");
            declare
               Equals : Natural := 0;
            begin
               for Index in Natural (Item.Place.First)
                 .. Natural'Min (Natural (Item.Place.Last), Source.Length)
               loop
                  pragma Loop_Invariant (Equals <= Index - Natural (Item.Place.First));
                  if Source.Text (Index) = '=' then
                     Equals := Equals + 1;
                  end if;
               end loop;
               Append_Copies (Output, Budget, '=', Equals);
            end;
            Append (Output, Budget, "]`");
            Why ("a long bracket ends at the first closing bracket with as many `=`" & Lexical);
         when Invalid_Long_String_Delimiter =>
            What ("");
            Place_Text;
            Append (Output, Budget, " is not followed by `[`");
            Why ("an opening long bracket is `[`, any number of `=`, and `[`" & Lexical);
         when Hexadecimal_Digit_Expected =>
            What ("");
            Place_Text;
            Append (Output, Budget, " needs a hexadecimal digit here");
            Why ("`\x` takes two hexadecimal digits, `\u{` at least one" & Lexical);
         when Missing_Opening_Brace =>
            What ("");
            Place_Text;
            Append (Output, Budget, ": `\u` must be followed by `{`");
            Why ("a UTF-8 escape is written `\u{XXX}`" & Lexical);
         when Missing_Closing_Brace =>
            What ("");
            Place_Text;
            Append (Output, Budget, " has no closing `}`");
            Why ("a UTF-8 escape is written `\u{XXX}`" & Lexical);
         when UTF_8_Value_Too_Large =>
            What ("the value in ");
            Place_Text;
            Append (Output, Budget, " is 2^31 or more");
            Why ("a UTF-8 escape encodes a value below 2^31" & Lexical);
         when Decimal_Escape_Too_Large =>
            What ("this decimal escape is more than 255");
            Why ("a decimal escape `\ddd` is one byte, from 0 to 255" & Lexical);
         when Invalid_Escape_Sequence =>
            What ("");
            Place_Text;
            Append (Output, Budget, " is not an escape sequence");
            Why ("the escapes are \a \b \f \n \r \t \v \\ \"" \' \z \xXX \ddd \u{XXX}, and \ "
                 & "before a line break" & Lexical);
         when Token_Expected | Token_Expected_To_Close =>
            What ("expected `" & Spelling (Item.Expected) & "`");
            if Item.Opener /= End_Of_Stream then
               Append (Output, Budget, " to close `" & Spelling (Item.Opener) & "`");
            end if;
            Append (Output, Budget, ", found ");
            Append_Found (Output, Budget, Item, Source);
            if Item.Opener /= End_Of_Stream then
               Why ("every `" & Spelling (Item.Opener) & "` needs its `"
                    & Spelling (Item.Expected) & "` (Lua 5.4 manual §"
                    & Section_Of (Item.Opener) & ")");
            else
               Why ("Lua's grammar needs `" & Spelling (Item.Expected)
                    & "` here (Lua 5.4 manual §9)");
            end if;
         when Unexpected_Symbol =>
            What ("");
            Append_Found (Output, Budget, Item, Source);
            if Item.In_Statement then
               Append (Output, Budget, " can't start a statement");
               Why ("a statement starts with a keyword, a name, `(` or `;` "
                    & "(Lua 5.4 manual §3.3)");
            else
               Append (Output, Budget, " can't start an expression");
               Why ("an expression starts with a value, a name, `(`, `{`, `function`, `...` "
                    & "or a unary operator (Lua 5.4 manual §3.4)");
            end if;
         when Not_A_Statement =>
            What ("this expression is not a statement");
            Why ("only function calls and assignments are statements (Lua 5.4 manual §3.3)");
         when Not_Assignable =>
            What ("this can't be assigned to");
            Why ("only names, fields and indexed expressions can be assigned to "
                 & "(Lua 5.4 manual §3.3.3)");
         when Function_Arguments_Expected =>
            What ("a method call needs its arguments here, found ");
            Append_Found (Output, Budget, Item, Source);
            Why ("`object:name` is only valid as a call, followed by `(`...`)`, a string or a "
                 & "table (Lua 5.4 manual §3.4.10)");
         when Name_Or_Vararg_Expected =>
            What ("");
            Append_Found (Output, Budget, Item, Source);
            Append (Output, Budget, " can't be a parameter");
            Why ("parameters are names, optionally followed by `...` last "
                 & "(Lua 5.4 manual §3.4.11)");
         when Equals_Or_In_Expected =>
            What ("expected `=` or `in` after the loop variable, found ");
            Append_Found (Output, Budget, Item, Source);
            Why ("a numeric `for` has `=`, a generic `for` has `in` (Lua 5.4 manual §3.3.5)");
         when Nesting_Too_Deep =>
            What ("nesting goes deeper than 200 levels here");
            Why ("PUC Lua's parser stops at 200 nested levels (LUAI_MAXCCALLS)");
         when Vararg_Outside_Vararg_Function =>
            What ("`...` is used in a function that has no `...` parameter");
            Why ("`...` can only be used directly inside a variadic function "
                 & "(Lua 5.4 manual §3.4.11)");
         when Unknown_Attribute =>
            What ("`<");
            if Item.Name /= No_Symbol then
               Append (Output, Budget, Text (Table, Item.Name));
            end if;
            Append (Output, Budget, ">` is not an attribute");
            Why ("the only attributes are <const> and <close> (Lua 5.4 manual §3.3.7)");
         when Multiple_To_Be_Closed =>
            What ("");
            Append_Name (Output, Budget, Table, Item.Name);
            Append (Output, Budget, " is a second <close> variable in this declaration");
            Why ("a list of variables can contain at most one to-be-closed variable "
                 & "(Lua 5.4 manual §3.3.7)");
         when Assignment_To_Constant =>
            What ("");
            Append_Name (Output, Budget, Table, Item.Name);
            Append (Output, Budget, " is assigned, but it is declared "
                                    & (if Item.Is_Close then "<close>" else "<const>"));
            if Item.Is_Close then
               Why ("a <close> variable behaves like a constant (Lua 5.4 manual §3.3.8)");
            else
               Why ("a <const> variable can't be assigned after its declaration "
                    & "(Lua 5.4 manual §3.3.7)");
            end if;
         when Label_Already_Defined =>
            What ("a label ");
            Append_Name (Output, Budget, Table, Item.Name);
            Append (Output, Budget, " is already visible here");
            Why ("a label should not be declared where a label with the same name is visible "
                 & "(Lua 5.4 manual §3.3.4)");
         when Goto_Into_Scope =>
            What ("`goto ");
            if Item.Name /= No_Symbol then
               Append (Output, Budget, Text (Table, Item.Name));
            end if;
            Append (Output, Budget, "` jumps into the scope of local ");
            Append_Name (Output, Budget, Table, Item.Other_Name);
            Why ("a goto can jump to a visible label only if it does not enter the scope of a "
                 & "local variable (Lua 5.4 manual §3.3.4)");
         when Break_Outside_Loop =>
            What ("`break` is not inside a loop");
            Why ("a break ends the innermost enclosing loop (Lua 5.4 manual §3.3.4)");
         when No_Visible_Label =>
            What ("no label ");
            Append_Name (Output, Budget, Table, Item.Name);
            Append (Output, Budget, " is visible from this `goto`");
            Why ("a label is visible in the block where it is defined, except inside nested "
                 & "functions (Lua 5.4 manual §3.3.4)");
         when Not_Enough_Memory =>
            What ("loading this chunk needs more memory than the limit allows");
            Why ("everything a load builds is charged to the memory limit");
         when Binary_Chunk =>
            What ("this file is a precompiled chunk");
            Why ("Pyro loads only Lua source text");
      end case;
   end Append_Explanation;

   --  Appends the fact of the because-link Index.
   procedure Append_Fact
     (Output : in out Character_Arrays.Growable_Array;
      Budget : in out Memory_Budget;
      Item   : Diagnostic;
      Table  : Symbol_Table;
      Index  : Link_Count)
   with
     Pre  => Is_Valid (Table) and then Names_Exist (Item, Table),
     Post => Limit (Budget) = Limit (Budget)'Old
   is
   begin
      case Item.What is
         when Token_Expected | Token_Expected_To_Close =>
            Append (Output, Budget, "`" & Spelling (Item.Opener) & "` opened here");
         when Multiple_To_Be_Closed =>
            Append (Output, Budget, "the first <close> variable is declared here");
         when Assignment_To_Constant =>
            Append_Name (Output, Budget, Table, Item.Name);
            Append (Output, Budget, " is declared "
                    & (if Item.Is_Close then "<close>" else "<const>") & " here");
         when Label_Already_Defined =>
            Append (Output, Budget, "the visible label ");
            Append_Name (Output, Budget, Table, Item.Name);
            Append (Output, Budget, " is defined here");
         when Goto_Into_Scope =>
            if Index = 1 then
               Append_Name (Output, Budget, Table, Item.Other_Name);
               Append (Output, Budget, " is declared here");
            else
               Append (Output, Budget, "the label ");
               Append_Name (Output, Budget, Table, Item.Name);
               Append (Output, Budget, " is here, inside its scope");
            end if;
         when others =>
            null;
      end case;
   end Append_Fact;

   procedure Append_Rich_Message
     (Output : in out Character_Arrays.Growable_Array;
      Budget : in out Memory_Budget;
      Item   : Diagnostic;
      Table  : Symbol_Table;
      Source : Sources.Source;
      File   : String)
   is
      Main   : Place;
      Margin : Positive;
   begin
      Append (Output, Budget, "refused: ");
      if not Item.Has_Place or else not Fits (Source, Item.Place) then
         Append (Output, Budget, File);
         Append (Output, Budget, [1 => ASCII.LF]);
         Append_Explanation (Output, Budget, Item, Table, Source);
         return;
      end if;
      Main := Locate
        (Source,
         (if Is_Not_Equal_Typo (Item, Source)
          then (First => Item.Place.First, Last => Item.Place.First + 1)
          else Item.Place));
      Margin := Image (Natural (Main.Line))'Length;
      for Index in 1 .. Item.Links loop
         pragma Loop_Invariant (Margin <= 10);
         if Fits (Source, Link_Place (Item, Index)) then
            Margin := Natural'Max
              (Margin, Image (Natural (Locate (Source, Link_Place (Item, Index)).Line))'Length);
         end if;
      end loop;
      Append_Place (Output, Budget, File, Main);
      Append (Output, Budget, [1 => ASCII.LF]);
      Append_Quote (Output, Budget, Source, Main, Margin);
      Append_Explanation (Output, Budget, Item, Table, Source);
      for Index in 1 .. Item.Links loop
         pragma Loop_Invariant (Limit (Budget) = Limit (Budget)'Loop_Entry);
         if Fits (Source, Link_Place (Item, Index)) then
            declare
               Link : constant Place := Locate (Source, Link_Place (Item, Index));
            begin
               Append (Output, Budget, " because: ");
               Append_Place (Output, Budget, File, Link);
               Append (Output, Budget, [1 => ASCII.LF]);
               Append_Quote (Output, Budget, Source, Link, Margin);
               Append (Output, Budget, " ");
               Append_Copies (Output, Budget, ' ', Margin + 3);
               Append_Fact (Output, Budget, Item, Table, Index);
               Append (Output, Budget, [1 => ASCII.LF]);
            end;
         end if;
      end loop;
   end Append_Rich_Message;

end Pyro.Diagnostics.Rendering;
