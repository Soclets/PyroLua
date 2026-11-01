--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  The parser's state and its small steps: reading tokens, reporting errors, building nodes,
--  recovering from errors and counting nesting levels.

with Pyro.Character_Arrays;
with Pyro.Diagnostic_Lists;
with Pyro.Diagnostics;    use Pyro.Diagnostics;
with Pyro.Lexer;          use Pyro.Lexer;
with Pyro.Tokens;         use Pyro.Tokens;

private package Pyro.Parser.Steps with SPARK_Mode => On, Always_Terminates is

   --  [limit LUAI_MAXCCALLS] PUC Lua raises "C stack overflow" when its count of nested C
   --  calls reaches 200. When luac parses, one call is already counted.
   Maximum_C_Calls : constant := 200;

   Calls_Before_Parsing : constant := 1;

   --  The nesting counted as PUC's parser counts it (lparser.c:enterlevel).
   Maximum_Level : constant := Maximum_C_Calls;

   type Nesting_Level is range 0 .. Maximum_Level;

   --  The parser's whole state. Parse moves the caller's symbols, tree and diagnostics in for
   --  the duration of the parse.
   type Parser_State is limited record
      Lexer         : Lexer_State;
      Symbols       : Symbol_Table;
      Tree          : Syntax_Tree;
      Problems      : Diagnostic_Lists.Growable_Array;
      Budget        : Memory_Budget;
      --  [puc llex.h:LexState.t] The current token, and the look-ahead one if any.
      Current       : Token;
      Ahead         : Token;
      Has_Ahead     : Boolean := False;
      --  The last byte of the last token consumed, for the spans of nodes.
      Previous_Last : Span_End := 0;
      --  A syntax error is unwinding the parse, to the nearest bracket that can recover.
      Failed        : Boolean := False;
      --  No recovery: the parse ends.
      Stopped       : Boolean := False;
      --  The function being parsed is vararg.
      In_Vararg     : Boolean := True;
      --  Recovery: the brackets opened since a syntax error, innermost last.
      Brackets      : Character_Arrays.Growable_Array;
   end record;

   --  [proof] The parser's parts are consistent with Source.
   function Valid (P : Parser_State; Source : Sources.Source) return Boolean
   with Ghost;

   --  [proof] What every parsing step keeps: validity, nodes only added, the list stack as it
   --  was, and the budget's limit.
   function Kept
     (P : Parser_State;
      Source        : Sources.Source;
      Old_Count     : Node_Index;
      Old_Pending   : List_Index;
      Old_Limit     : Byte_Count) return Boolean
   is (Valid (P, Source)
       and then Node_Count (P.Tree) >= Old_Count
       and then Pending (P.Tree) = Old_Pending
       and then Limit (P.Budget) = Old_Limit)
   with Ghost;

   --  Reporting

   --  Adds Item to the diagnostics. Without memory for it, the parse stops.
   procedure Report
     (Problems : in out Diagnostic_Lists.Growable_Array;
      Budget   : in out Memory_Budget;
      Item     : Diagnostic;
      Failed   : in out Boolean;
      Stopped  : in out Boolean)
   with
     Post =>
       Limit (Budget) = Limit (Budget)'Old
       and then (if Failed'Old then Failed)
       and then (if Stopped'Old then Stopped)
       and then (if Stopped and then not Stopped'Old then Failed);

   --  Stops the parse because the memory budget ran out.
   procedure Stop_For_Memory (P : in out Parser_State; Source : Sources.Source)
   with
     Pre  => Valid (P, Source),
     Post =>
       Valid (P, Source)
       and then P.Stopped
       and then Node_Count (P.Tree) = Node_Count (P.Tree)'Old
       and then Pending (P.Tree) = Pending (P.Tree)'Old
       and then Limit (P.Budget) = Limit (P.Budget)'Old;

   --  The span of the current token (a point at the end of the chunk).
   function Current_Span (P : Parser_State) return Span
   is (First => P.Current.First,
       Last  => (if P.Current.Kind = End_Of_Stream then P.Current.First - 1 else P.Current.Last))
   with Pre => P.Current.Last <= Span_End'Last;

   --  Fills in Item as luaX_syntaxerror and luaK_semerror describe the current token: PUC's
   --  current line, and the token as "near" text when Near.
   procedure Describe_Current
     (P : in out Parser_State; Source : Sources.Source; Item : in out Diagnostic; Near : Boolean)
   with
     Pre  => Valid (P, Source),
     Post =>
       Valid (P, Source)
       and then Node_Count (P.Tree) = Node_Count (P.Tree)'Old
       and then Pending (P.Tree) = Pending (P.Tree)'Old
       and then P.Failed = P.Failed'Old
       and then P.Stopped = P.Stopped'Old
       and then Limit (P.Budget) = Limit (P.Budget)'Old
       and then Count (P.Symbols) >= Count (P.Symbols)'Old;

   --  Reports an error about the current token that does not stop parsing.
   procedure Report_Current
     (P : in out Parser_State; Source : Sources.Source; Template : Diagnostic; Near : Boolean)
   with
     Pre  => Valid (P, Source),
     Post =>
       Valid (P, Source)
       and then Node_Count (P.Tree) = Node_Count (P.Tree)'Old
       and then Pending (P.Tree) = Pending (P.Tree)'Old
       and then (if P.Failed'Old then P.Failed)
       and then (if P.Stopped'Old then P.Stopped)
       and then Limit (P.Budget) = Limit (P.Budget)'Old
       and then Count (P.Symbols) >= Count (P.Symbols)'Old;

   --  [puc llex.c:luaX_syntaxerror] Reports a syntax error at the current token and starts
   --  unwinding (only the first error of an unwinding is reported).
   procedure Syntax_Error (P : in out Parser_State; Source : Sources.Source; Template : Diagnostic)
   with
     Pre  => Valid (P, Source),
     Post =>
       Valid (P, Source)
       and then P.Failed
       and then (if P.Stopped'Old then P.Stopped)
       and then Node_Count (P.Tree) = Node_Count (P.Tree)'Old
       and then Pending (P.Tree) = Pending (P.Tree)'Old
       and then Limit (P.Budget) = Limit (P.Budget)'Old
       and then Count (P.Symbols) >= Count (P.Symbols)'Old;

   --  [puc lparser.c:error_expected]
   procedure Error_Expected
     (P : in out Parser_State;
      Source : Sources.Source;
      Expected : Spelled_Token)
   with
     Pre  => Valid (P, Source),
     Post =>
       Valid (P, Source)
       and then P.Failed
       and then (if P.Stopped'Old then P.Stopped)
       and then Node_Count (P.Tree) = Node_Count (P.Tree)'Old
       and then Pending (P.Tree) = Pending (P.Tree)'Old
       and then Limit (P.Budget) = Limit (P.Budget)'Old
       and then Count (P.Symbols) >= Count (P.Symbols)'Old;

   --  Reading tokens

   --  [puc llex.c:luaX_next] Moves to the next token. A lexical error stops the parse.
   procedure Next (P : in out Parser_State; Source : Sources.Source)
   with
     Pre  => Valid (P, Source),
     Post =>
       Valid (P, Source)
       and then Node_Count (P.Tree) = Node_Count (P.Tree)'Old
       and then Pending (P.Tree) = Pending (P.Tree)'Old
       and then (if P.Failed'Old then P.Failed)
       and then (if P.Stopped'Old then P.Stopped)
       and then Limit (P.Budget) = Limit (P.Budget)'Old
       and then Count (P.Symbols) >= Count (P.Symbols)'Old;

   --  [puc llex.c:luaX_lookahead]
   procedure Look_Ahead (P : in out Parser_State; Source : Sources.Source)
   with
     Pre  => Valid (P, Source) and then not P.Has_Ahead,
     Post =>
       Valid (P, Source)
       and then P.Has_Ahead
       and then Node_Count (P.Tree) = Node_Count (P.Tree)'Old
       and then Pending (P.Tree) = Pending (P.Tree)'Old
       and then (if P.Failed'Old then P.Failed)
       and then (if P.Stopped'Old then P.Stopped)
       and then Limit (P.Budget) = Limit (P.Budget)'Old
       and then Count (P.Symbols) >= Count (P.Symbols)'Old;

   --  [puc lparser.c:testnext]
   procedure Test_Next
     (P : in out Parser_State; Source : Sources.Source; Kind : Token_Kind; Found : out Boolean)
   with
     Pre  => Valid (P, Source),
     Post =>
       Valid (P, Source)
       and then Node_Count (P.Tree) = Node_Count (P.Tree)'Old
       and then Pending (P.Tree) = Pending (P.Tree)'Old
       and then (if P.Failed'Old then P.Failed and then not Found)
       and then (if P.Stopped'Old then P.Stopped)
       and then Limit (P.Budget) = Limit (P.Budget)'Old
       and then Count (P.Symbols) >= Count (P.Symbols)'Old;

   --  [puc lparser.c:checknext]
   procedure Check_Next (P : in out Parser_State; Source : Sources.Source; Kind : Spelled_Token)
   with
     Pre  => Valid (P, Source),
     Post =>
       Valid (P, Source)
       and then Node_Count (P.Tree) = Node_Count (P.Tree)'Old
       and then Pending (P.Tree) = Pending (P.Tree)'Old
       and then (if P.Failed'Old then P.Failed)
       and then (if P.Stopped'Old then P.Stopped)
       and then Limit (P.Budget) = Limit (P.Budget)'Old
       and then Count (P.Symbols) >= Count (P.Symbols)'Old;

   --  [puc lparser.c:check_match] Consumes What, which closes Who (the token at Opener, on
   --  line Where).
   procedure Check_Match
     (P : in out Parser_State;
      Source : Sources.Source;
      What   : Spelled_Token;
      Who    : Spelled_Token;
      Where  : Line_Number;
      Opener : Span)
   with
     Pre  => Valid (P, Source),
     Post =>
       Valid (P, Source)
       and then Node_Count (P.Tree) = Node_Count (P.Tree)'Old
       and then Pending (P.Tree) = Pending (P.Tree)'Old
       and then (if P.Failed'Old then P.Failed)
       and then (if P.Stopped'Old then P.Stopped)
       and then Limit (P.Budget) = Limit (P.Budget)'Old
       and then Count (P.Symbols) >= Count (P.Symbols)'Old;

   --  [puc lparser.c:check_match] Unless the parse has failed, requires What (closing Who,
   --  the token at Opener on line Where) to be the current token, without consuming it.
   procedure Expect_Closer
     (P      : in out Parser_State;
      Source : Sources.Source;
      What   : Spelled_Token;
      Who    : Spelled_Token;
      Where  : Line_Number;
      Opener : Span)
   with
     Pre  => Valid (P, Source),
     Post =>
       Valid (P, Source)
       and then (P.Failed or else P.Current.Kind = What)
       and then Node_Count (P.Tree) = Node_Count (P.Tree)'Old
       and then Pending (P.Tree) = Pending (P.Tree)'Old
       and then (if P.Failed'Old then P.Failed)
       and then (if P.Stopped'Old then P.Stopped)
       and then Limit (P.Budget) = Limit (P.Budget)'Old;

   --  [puc lparser.c:str_checkname] Consumes a name and gives its symbol.
   procedure Check_Name
     (P : in out Parser_State;
      Source : Sources.Source;
      Symbol : out Symbol_Index)
   with
     Pre  => Valid (P, Source),
     Post =>
       Valid (P, Source)
       and then Symbol <= Count (P.Symbols)
       and then Node_Count (P.Tree) = Node_Count (P.Tree)'Old
       and then Pending (P.Tree) = Pending (P.Tree)'Old
       and then (if P.Failed'Old then P.Failed)
       and then (if P.Stopped'Old then P.Stopped)
       and then Limit (P.Budget) = Limit (P.Budget)'Old
       and then Count (P.Symbols) >= Count (P.Symbols)'Old;

   --  [puc lparser.c:block_follow]
   function Block_Follow (P : Parser_State; With_Until : Boolean) return Boolean
   is (case P.Current.Kind is
         when Keyword_Else | Keyword_Elseif | Keyword_End | End_Of_Stream => True,
         when Keyword_Until => With_Until,
         when others => False);

   --  Building nodes

   --  A node of Kind starting at First, on Line, ending with the last token consumed.
   function Shape
     (P : Parser_State; Kind : Node_Kind; First : Source_Position; Line : Line_Number) return Node
   is ((Kind => Kind, First => First, Last => P.Previous_Last, Line => Line, others => <>));

   --  Adds Item (whose children are nodes already) as a node; memory exhaustion stops the parse.
   procedure Make
     (P : in out Parser_State;
      Source : Sources.Source;
      Item : Node;
      Result : out Node_Index)
   with
     Pre  =>
       Valid (P, Source)
       and then (for all Slot in Child_Slot => Child_Of (Item, Slot) <= Node_Count (P.Tree)),
     Post =>
       Valid (P, Source)
       and then Node_Count (P.Tree) >= Node_Count (P.Tree)'Old
       and then Pending (P.Tree) = Pending (P.Tree)'Old
       and then Result <= Node_Count (P.Tree)
       and then (if P.Failed'Old then P.Failed)
       and then (if P.Stopped'Old then P.Stopped)
       and then Limit (P.Budget) = Limit (P.Budget)'Old;

   --  Adds Item as a node whose list is what waits above Mark.
   procedure Make_List
     (P : in out Parser_State; Source : Sources.Source; Item : Node; Mark : List_Index;
      Result : out Node_Index)
   with
     Pre  =>
       Valid (P, Source)
       and then Mark <= Pending (P.Tree)
       and then (for all Slot in Child_Slot => Child_Of (Item, Slot) <= Node_Count (P.Tree)),
     Post =>
       Valid (P, Source)
       and then Node_Count (P.Tree) >= Node_Count (P.Tree)'Old
       and then Pending (P.Tree) = Mark
       and then Result <= Node_Count (P.Tree)
       and then (if P.Failed'Old then P.Failed)
       and then (if P.Stopped'Old then P.Stopped)
       and then Limit (P.Budget) = Limit (P.Budget)'Old;

   --  Puts Item (if it is a node) on the list being built.
   procedure Add_To_List (P : in out Parser_State; Source : Sources.Source; Item : Node_Index)
   with
     Pre  => Valid (P, Source) and then Item <= Node_Count (P.Tree),
     Post =>
       Valid (P, Source)
       and then Node_Count (P.Tree) = Node_Count (P.Tree)'Old
       and then Pending (P.Tree) >= Pending (P.Tree)'Old
       and then (if P.Failed'Old then P.Failed)
       and then (if P.Stopped'Old then P.Stopped)
       and then Limit (P.Budget) = Limit (P.Budget)'Old;

   --  Recovery

   function Closer_Of (Opener : Token_Kind) return Token_Kind
   is (case Opener is
         when Left_Parenthesis => Right_Parenthesis,
         when Left_Bracket     => Right_Bracket,
         when others           => Right_Brace);

   function Is_Opening (Kind : Token_Kind) return Boolean
   is (Kind in Left_Parenthesis | Left_Bracket | Left_Brace);

   function Is_Closing (Kind : Token_Kind) return Boolean
   is (Kind in Right_Parenthesis | Right_Bracket | Right_Brace);

   --  After a syntax error inside a bracket opened with Opener: when its closing bracket is
   --  intact (the following tokens nest properly up to it), skips to it, leaving it as the
   --  current token, and recovers. Otherwise the parse stops.
   procedure Recover (P : in out Parser_State; Source : Sources.Source; Opener : Token_Kind)
   with
     Pre  =>
       Valid (P, Source)
       and then Is_Opening (Opener)
       and then (P.Failed or else P.Current.Kind = Closer_Of (Opener)),
     Post =>
       Valid (P, Source)
       and then Node_Count (P.Tree) = Node_Count (P.Tree)'Old
       and then Pending (P.Tree) = Pending (P.Tree)'Old
       and then (if P.Stopped'Old then P.Stopped)
       and then (if not P.Failed then P.Current.Kind = Closer_Of (Opener))
       and then Limit (P.Budget) = Limit (P.Budget)'Old;

   --  Levels

   --  [puc lparser.c:enterlevel] Counts one more level; at PUC's limit, reports "C stack
   --  overflow" (which has no line in PUC Lua) at the current token and stops.
   procedure Enter_Level
     (P : in out Parser_State;
      Source : Sources.Source;
      Level : Nesting_Level;
      Overflow : out Boolean)
   with
     Pre  => Valid (P, Source),
     Post =>
       Valid (P, Source)
       and then (if not Overflow then Level < Maximum_Level - Calls_Before_Parsing - 1
                 else P.Stopped)
       and then Node_Count (P.Tree) = Node_Count (P.Tree)'Old
       and then Pending (P.Tree) = Pending (P.Tree)'Old
       and then (if P.Failed'Old then P.Failed)
       and then (if P.Stopped'Old then P.Stopped)
       and then Limit (P.Budget) = Limit (P.Budget)'Old;

   --  Sets whether the function being parsed is vararg.
   procedure Set_Vararg (P : in out Parser_State; Source : Sources.Source; Value : Boolean)
   with
     Pre  => Valid (P, Source),
     Post =>
       Valid (P, Source)
       and then P.In_Vararg = Value
       and then Node_Count (P.Tree) = Node_Count (P.Tree)'Old
       and then Pending (P.Tree) = Pending (P.Tree)'Old
       and then P.Failed = P.Failed'Old
       and then P.Stopped = P.Stopped'Old
       and then Limit (P.Budget) = Limit (P.Budget)'Old;

   --  [puc lparser.c:getlocalattribute] True when Symbol is the name Name.
   function Is_Attribute
     (P      : Parser_State;
      Source : Sources.Source;
      Symbol : Symbol_Index;
      Name   : String) return Boolean
   with Pre => Valid (P, Source) and then Symbol <= Count (P.Symbols);

   --  Moves the caller's symbols, tree and diagnostics into P and reads the first token.
   procedure Begin_Parse
     (P : in out Parser_State;
      Source   : Sources.Source;
      Symbols  : in out Symbol_Table;
      Budget   : Memory_Budget;
      Tree     : in out Syntax_Tree;
      Problems : in out Diagnostic_Lists.Growable_Array)
   with
     Pre  =>
       Is_Valid (Symbols)
       and then Is_Well_Formed (Tree)
       and then Is_Released (P.Symbols)
       and then Is_Released (P.Tree)
       and then Diagnostic_Lists.Is_Released (P.Problems)
       and then Is_Released (P.Lexer)
       and then Character_Arrays.Is_Released (P.Brackets)
       and then Is_Valid (P.Symbols)
       and then Is_Well_Formed (P.Tree),
     Post =>
       Valid (P, Source)
       and then Is_Released (Symbols)
       and then Is_Valid (Symbols)
       and then Is_Released (Tree)
       and then Is_Well_Formed (Tree)
       and then Diagnostic_Lists.Is_Released (Problems)
       and then Limit (P.Budget) = Limit (Budget);

   --  Moves the symbols, tree and diagnostics back to the caller and releases P's memory.
   procedure End_Parse
     (P : in out Parser_State;
      Source   : Sources.Source;
      Symbols  : in out Symbol_Table;
      Budget   : out Memory_Budget;
      Tree     : in out Syntax_Tree;
      Problems : in out Diagnostic_Lists.Growable_Array)
   with
     Pre  =>
       Valid (P, Source)
       and then Is_Released (Symbols)
       and then Is_Released (Tree)
       and then Diagnostic_Lists.Is_Released (Problems)
       and then Is_Valid (Symbols)
       and then Is_Well_Formed (Tree),
     Post =>
       Is_Valid (Symbols)
       and then Is_Well_Formed (Tree)
       and then Node_Count (Tree) = Node_Count (P.Tree)'Old
       and then Limit (Budget) = Limit (P.Budget)'Old
       and then Is_Released (P.Symbols)
       and then Is_Released (P.Tree)
       and then Diagnostic_Lists.Is_Released (P.Problems)
       and then Is_Released (P.Lexer)
       and then Character_Arrays.Is_Released (P.Brackets);

end Pyro.Parser.Steps;
