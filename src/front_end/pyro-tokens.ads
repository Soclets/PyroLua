--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  Lua 5.4 tokens: their kinds, payloads and fixed spellings.

with Interfaces;
with Pyro.Sources; use Pyro.Sources;
with Pyro.Symbols; use Pyro.Symbols;

package Pyro.Tokens with SPARK_Mode => On, Always_Terminates is

   --  [puc llex.h:RESERVED] The kinds of token, in PUC Lua's order for keywords and multi-byte
   --  symbols, then single-byte symbols.
   type Token_Kind is
     (Keyword_And, Keyword_Break, Keyword_Do, Keyword_Else, Keyword_Elseif, Keyword_End,
      Keyword_False, Keyword_For, Keyword_Function, Keyword_Goto, Keyword_If, Keyword_In,
      Keyword_Local, Keyword_Nil, Keyword_Not, Keyword_Or, Keyword_Repeat, Keyword_Return,
      Keyword_Then, Keyword_True, Keyword_Until, Keyword_While,
      Double_Slash, Double_Dot, Triple_Dot, Equal_Equal, Greater_Equal, Less_Equal, Not_Equal,
      Shift_Left, Shift_Right, Double_Colon, End_Of_Stream,
      Float_Numeral, Integer_Numeral, Name, String_Literal,
      Plus_Sign, Minus_Sign, Asterisk, Slash, Percent_Sign, Caret, Number_Sign, Ampersand,
      Tilde, Vertical_Bar, Less_Than, Greater_Than, Equals_Sign, Left_Parenthesis,
      Right_Parenthesis, Left_Brace, Right_Brace, Left_Bracket, Right_Bracket, Semicolon, Colon,
      Comma, Dot,
      --  Any other single byte, which only the error "unexpected symbol" accepts.
      Other_Byte);

   subtype Keyword is Token_Kind range Keyword_And .. Keyword_While;

   --  Tokens whose text varies (PUC prints their text, not their kind, in messages).
   subtype Token_With_Text is Token_Kind range Float_Numeral .. String_Literal;

   --  Tokens written as one byte.
   subtype Single_Byte_Token is Token_Kind range Plus_Sign .. Other_Byte;

   --  The count of tokens read so far from a chunk, the first being 1. PUC Lua raises each
   --  error while looking at some token; its ordinal orders errors as PUC would find them.
   type Token_Ordinal is range 0 .. Maximum_Source_Length + 2;

   --  A token: its kind, where it is, and its value.
   type Token is record
      Kind : Token_Kind := End_Of_Stream;
      --  The bytes of the token in the source, First .. Last (Last = First - 1 at the end).
      First : Source_Position := 1;
      Last  : Span_End := 0;
      --  PUC Lua's line number once the token is read: the line of its last byte.
      Line : Line_Number := 1;
      --  The line of its first byte.
      First_Line : Line_Number := 1;
      Ordinal    : Token_Ordinal := 0;
      --  Names and strings: the (decoded) bytes.
      Symbol : Symbol_Index := No_Symbol;
      --  Integer numerals.
      Integer_Value : Interfaces.Integer_64 := 0;
      --  Float numerals, as IEEE 754 binary64 bits.
      Float_Bits : Interfaces.Unsigned_64 := 0;
      --  Other_Byte: the byte.
      Byte : Character := ASCII.NUL;
   end record;

   --  [puc llex.c:luaX_tokens] The spelling of a token kind with a fixed spelling; for the
   --  kinds whose text varies, PUC's placeholder ("<name>", "<string>" ...).
   function Spelling (Kind : Token_Kind) return String
   with Global => null, Pre => Kind /= Other_Byte, Post => Spelling'Result'Length in 1 .. 9;

   --  The single byte of a single-byte token kind other than Other_Byte.
   function Byte_Of (Kind : Single_Byte_Token) return Character
   with Global => null;

   --  The single-byte token kind for Byte (Other_Byte if it has no meaning of its own).
   function Kind_Of_Byte (Byte : Character) return Single_Byte_Token
   with Global => null;

end Pyro.Tokens;
