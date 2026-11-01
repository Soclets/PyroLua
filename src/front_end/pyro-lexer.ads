--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  Tokenizer for Lua 5.4 source text.

with Pyro.Character_Arrays;
with Pyro.Diagnostics;    use Pyro.Diagnostics;
with Pyro.Memory_Budgets; use Pyro.Memory_Budgets;
with Pyro.Sources;        use Pyro.Sources;
with Pyro.Symbols;        use Pyro.Symbols;
with Pyro.Tokens;         use Pyro.Tokens;

package Pyro.Lexer with SPARK_Mode => On, Always_Terminates is

   --  [puc llex.h:LexState] Where the lexer is in a chunk, and the text of the token it read
   --  last. It owns heap memory: release it with Clear.
   type Lexer_State is limited private
   with Default_Initial_Condition => not Failed (Lexer_State);

   --  The state is consistent with Source. Every operation keeps this true.
   function Is_Valid (Lexer : Lexer_State; Source : Sources.Source) return Boolean
   with Global => null;

   --  A lexical error (or running out of memory) stopped the lexer.
   function Failed (Lexer : Lexer_State) return Boolean
   with Global => null;

   --  The error that stopped the lexer.
   function Error (Lexer : Lexer_State) return Diagnostic
   with Global => null, Pre => Failed (Lexer);

   --  [puc llex.h:LexState.linenumber] The current line: the line of the last byte read.
   function Line (Lexer : Lexer_State) return Line_Number
   with Global => null;

   --  The ordinal of the last token read (0 before the first).
   function Ordinal (Lexer : Lexer_State) return Token_Ordinal
   with Global => null;

   --  A lexer at the start of a chunk.
   procedure Start
     (Lexer : in out Lexer_State; Source : Sources.Source; Budget : in out Memory_Budget)
   with
     Global => null,
     Post   =>
       Is_Valid (Lexer, Source)
       and then not Failed (Lexer)
       and then Ordinal (Lexer) = 0
       and then Limit (Budget) = Limit (Budget)'Old;

   --  [puc llex.c:llex] Reads the next token. On a lexical error the lexer has Failed, with
   --  the error PUC Lua would raise, and Result is End_Of_Stream.
   procedure Next_Token
     (Lexer   : in out Lexer_State;
      Source  : Sources.Source;
      Symbols : in out Symbol_Table;
      Budget  : in out Memory_Budget;
      Result  : out Token)
   with
     Global => null,
     Pre    => Is_Valid (Lexer, Source) and then Is_Valid (Symbols) and then not Failed (Lexer),
     Post   =>
       Is_Valid (Lexer, Source)
       and then Is_Valid (Symbols)
       and then Count (Symbols) >= Count (Symbols)'Old
       and then Result.Symbol <= Count (Symbols)
       and then Natural (Result.Last) <= Source.Length
       and then Result.Ordinal = Ordinal (Lexer)
       and then Limit (Budget) = Limit (Budget)'Old;

   --  [puc llex.c:txtToken] The text of the token read last, as PUC Lua quotes it in a
   --  message (up to its first NUL byte), as a symbol. No_Symbol if memory ran out.
   procedure Token_Text
     (Lexer   : Lexer_State;
      Symbols : in out Symbol_Table;
      Budget  : in out Memory_Budget;
      Symbol  : out Symbol_Index)
   with
     Global => null,
     Pre    => Is_Valid (Symbols),
     Post   =>
       Is_Valid (Symbols)
       and then Count (Symbols) >= Count (Symbols)'Old
       and then Symbol <= Count (Symbols)
       and then Limit (Budget) = Limit (Budget)'Old;

   --  Releases the lexer's memory.
   procedure Clear (Lexer : in out Lexer_State; Budget : in out Memory_Budget)
   with Global => null, Post => Is_Released (Lexer) and then Limit (Budget) = Limit (Budget)'Old;

   --  True when the lexer holds no heap memory.
   function Is_Released (Lexer : Lexer_State) return Boolean
   with Global => null;

private

   type Lexer_State is limited record
      --  The next byte to read ("current" in llex.c), or Length + 1 at the end.
      Position : Source_Position := 1;
      Line     : Line_Number := 1;
      --  [puc llex.h:LexState.buff] The bytes of the token being read.
      Buffer   : Character_Arrays.Growable_Array;
      Ordinal  : Token_Ordinal := 0;
      Stopped  : Boolean := False;
      Problem  : Diagnostic;
   end record;

   function Failed (Lexer : Lexer_State) return Boolean is (Lexer.Stopped);

   function Error (Lexer : Lexer_State) return Diagnostic is (Lexer.Problem);

   function Line (Lexer : Lexer_State) return Line_Number is (Lexer.Line);

   function Ordinal (Lexer : Lexer_State) return Token_Ordinal is (Lexer.Ordinal);

   function Is_Released (Lexer : Lexer_State) return Boolean
   is (Character_Arrays.Is_Released (Lexer.Buffer));

end Pyro.Lexer;
