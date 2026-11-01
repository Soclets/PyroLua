--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  Lua 5.4 tokens: their kinds, payloads and fixed spellings.

package body Pyro.Tokens with SPARK_Mode => On is

   function Spelling (Kind : Token_Kind) return String is
   begin
      case Kind is
         when Keyword_And      => return "and";
         when Keyword_Break    => return "break";
         when Keyword_Do       => return "do";
         when Keyword_Else     => return "else";
         when Keyword_Elseif   => return "elseif";
         when Keyword_End      => return "end";
         when Keyword_False    => return "false";
         when Keyword_For      => return "for";
         when Keyword_Function => return "function";
         when Keyword_Goto     => return "goto";
         when Keyword_If       => return "if";
         when Keyword_In       => return "in";
         when Keyword_Local    => return "local";
         when Keyword_Nil      => return "nil";
         when Keyword_Not      => return "not";
         when Keyword_Or       => return "or";
         when Keyword_Repeat   => return "repeat";
         when Keyword_Return   => return "return";
         when Keyword_Then     => return "then";
         when Keyword_True     => return "true";
         when Keyword_Until    => return "until";
         when Keyword_While    => return "while";
         when Double_Slash     => return "//";
         when Double_Dot       => return "..";
         when Triple_Dot       => return "...";
         when Equal_Equal      => return "==";
         when Greater_Equal    => return ">=";
         when Less_Equal       => return "<=";
         when Not_Equal        => return "~=";
         when Shift_Left       => return "<<";
         when Shift_Right      => return ">>";
         when Double_Colon     => return "::";
         when End_Of_Stream    => return "<eof>";
         when Float_Numeral    => return "<number>";
         when Integer_Numeral  => return "<integer>";
         when Name             => return "<name>";
         when String_Literal   => return "<string>";
         when Single_Byte_Token => return [1 => Byte_Of (Kind)];
      end case;
   end Spelling;

   function Byte_Of (Kind : Single_Byte_Token) return Character is
   begin
      case Kind is
         when Plus_Sign         => return '+';
         when Minus_Sign        => return '-';
         when Asterisk          => return '*';
         when Slash             => return '/';
         when Percent_Sign      => return '%';
         when Caret             => return '^';
         when Number_Sign       => return '#';
         when Ampersand         => return '&';
         when Tilde             => return '~';
         when Vertical_Bar      => return '|';
         when Less_Than         => return '<';
         when Greater_Than      => return '>';
         when Equals_Sign       => return '=';
         when Left_Parenthesis  => return '(';
         when Right_Parenthesis => return ')';
         when Left_Brace        => return '{';
         when Right_Brace       => return '}';
         when Left_Bracket      => return '[';
         when Right_Bracket     => return ']';
         when Semicolon         => return ';';
         when Colon             => return ':';
         when Comma             => return ',';
         when Dot               => return '.';
         when Other_Byte        => return ASCII.NUL;
      end case;
   end Byte_Of;

   function Kind_Of_Byte (Byte : Character) return Single_Byte_Token is
   begin
      for Kind in Plus_Sign .. Dot loop
         if Byte_Of (Kind) = Byte then
            return Kind;
         end if;
      end loop;
      return Other_Byte;
   end Kind_Of_Byte;

end Pyro.Tokens;
