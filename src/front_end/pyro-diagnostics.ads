--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  Diagnostics: what went wrong in a chunk, recorded for both the rich and the Lua-style report.

with Pyro.Character_Arrays;
with Pyro.Memory_Budgets; use Pyro.Memory_Budgets;
with Pyro.Sources; use Pyro.Sources;
with Pyro.Symbols; use Pyro.Symbols;
with Pyro.Tokens;  use Pyro.Tokens;

package Pyro.Diagnostics with SPARK_Mode => On, Always_Terminates is

   --  Every problem the front end reports.
   type Problem is
     (
      --  Lexical errors (llex.c).
      Malformed_Number, Unfinished_String, Unfinished_Long_String, Unfinished_Long_Comment,
      Invalid_Long_String_Delimiter, Hexadecimal_Digit_Expected, Missing_Opening_Brace,
      Missing_Closing_Brace, UTF_8_Value_Too_Large, Decimal_Escape_Too_Large,
      Invalid_Escape_Sequence,
      --  Syntax errors (lparser.c).
      Token_Expected, Token_Expected_To_Close, Unexpected_Symbol, Not_A_Statement,
      Not_Assignable, Function_Arguments_Expected, Name_Or_Vararg_Expected,
      Equals_Or_In_Expected, Nesting_Too_Deep,
      --  Errors the parser finds that are not grammar errors.
      Vararg_Outside_Vararg_Function, Unknown_Attribute, Multiple_To_Be_Closed,
      --  Errors the resolver finds.
      Assignment_To_Constant, Label_Already_Defined, Goto_Into_Scope, Break_Outside_Loop,
      No_Visible_Label,
      --  Compile-time limits (lparser.c, lcode.c).
      Too_Many_Registers, Too_Many_Local_Variables, Too_Many_Upvalues,
      Control_Structure_Too_Long,
      --  Errors of the whole load.
      Not_Enough_Memory, Binary_Chunk, Internal_Error);

   --  Problems that end the run: nothing after them can be reported with certainty.
   subtype Lexical_Problem is Problem range Malformed_Number .. Invalid_Escape_Sequence;

   --  A run of source bytes, First .. Last; Last = First - 1 for a point (the end of the chunk).
   type Span is record
      First : Source_Position := 1;
      Last  : Span_End := 0;
   end record;

   --  Tokens with a fixed spelling: the ones a message can say were expected.
   subtype Spelled_Token is Token_Kind range Keyword_And .. Dot;

   --  What PUC Lua prints after "near" in a syntax error.
   type Near_Kind is
     (No_Near,     --  semantic errors: no "near" part
      Near_Token,  --  a token with a fixed spelling (or a single byte)
      Near_Text);  --  the text of the token being read, quoted

   --  When PUC Lua would raise an error, for picking the first one. At the same token, a lexical
   --  error comes first (raised while reading it), then the resolver's (raised before the
   --  parser looks at it), then the parser's.
   type Phase is (Lexing, Resolving, Parsing);

   type Detection_Point is record
      Ordinal : Token_Ordinal := 0;
      During  : Phase := Parsing;
   end record;

   --  True when Left comes before Right.
   function Before (Left, Right : Detection_Point) return Boolean
   is (Left.Ordinal < Right.Ordinal
       or else (Left.Ordinal = Right.Ordinal and then Left.During < Right.During));

   --  The number of "because" links of a diagnostic (at most two).
   type Link_Count is range 0 .. 2;

   --  A position in a list of diagnostics.
   type Diagnostic_Position is range 1 .. 2 ** 20;

   --  One problem, with everything both reports need.
   type Diagnostic is record
      What : Problem := Not_Enough_Memory;

      --  The rich report: where the problem is (absent for problems of the whole load), the
      --  places of its "because" links, and the pieces the message names.
      Has_Place   : Boolean := False;
      Place       : Span := (First => 1, Last => 0);
      Links       : Link_Count := 0;
      First_Link  : Span := (First => 1, Last => 0);
      Second_Link : Span := (First => 1, Last => 0);
      --  A variable, label or attribute name, and a second name (the local of Goto_Into_Scope).
      Name       : Symbol_Index := No_Symbol;
      Other_Name : Symbol_Index := No_Symbol;
      --  Too_Many_Local_Variables and Too_Many_Upvalues: the limit is hit in the main function
      --  (otherwise Other_Line is the line of the function).
      In_Main_Function : Boolean := False;
      --  The token found (Unexpected_Symbol, Token_Expected ...), with its byte for Other_Byte.
      Found      : Token_Kind := End_Of_Stream;
      Found_Byte : Character := ASCII.NUL;
      --  The token that was expected, and the token it would close.
      Expected : Spelled_Token := End_Of_Stream;
      Opener   : Spelled_Token := End_Of_Stream;
      --  Assignment_To_Constant: the variable is <close> rather than <const>.
      Is_Close : Boolean := False;
      --  The parser was reading a statement rather than an expression (Unexpected_Symbol).
      In_Statement : Boolean := False;

      --  The Lua-style report: PUC Lua's line (absent for "C stack overflow" and the problems
      --  of the whole load), "near" part, the line a message mentions, and when PUC raises it.
      Has_Lua_Line : Boolean := False;
      Lua_Line     : Line_Number := 1;
      Near         : Near_Kind := No_Near;
      Near_Token   : Token_Kind := End_Of_Stream;
      Near_Byte    : Character := ASCII.NUL;
      Near_Text    : Symbol_Index := No_Symbol;
      Other_Line   : Line_Number := 1;
      Detection    : Detection_Point := (Ordinal => 0, During => Parsing);
   end record;

   --  The place of "because" link Index of Item.
   function Link_Place (Item : Diagnostic; Index : Link_Count) return Span
   is (if Index = 2 then Item.Second_Link else Item.First_Link);

   --  The symbols a diagnostic names exist in Table.
   function Names_Exist (Item : Diagnostic; Table : Symbol_Table) return Boolean
   is (Item.Name <= Count (Table)
       and then Item.Other_Name <= Count (Table)
       and then Item.Near_Text <= Count (Table))
   with Global => null;

   --  [puc ldebug.c:luaG_addinfo] Appends Item as PUC Lua writes it, without a line break:
   --  "chunk:line: message near 'text'", or just the message when PUC gives no place.
   procedure Append_Lua_Message
     (Output : in out Character_Arrays.Growable_Array;
      Budget : in out Memory_Budget;
      Item   : Diagnostic;
      Table  : Symbol_Table;
      Source : Sources.Source)
   with
     Global => null,
     Pre    => Is_Valid (Table) and then Names_Exist (Item, Table),
     Post   => Limit (Budget) = Limit (Budget)'Old;

   --  Appends Text to Output, as far as Budget allows.
   procedure Append
     (Output : in out Character_Arrays.Growable_Array;
      Budget : in out Memory_Budget;
      Text   : String)
   with Global => null, Post => Limit (Budget) = Limit (Budget)'Old;

   --  The decimal digits of Value.
   function Image (Value : Natural) return String
   with Global => null, Post => Image'Result'First = 1 and then Image'Result'Length in 1 .. 10;

end Pyro.Diagnostics;
