--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  Recursive-descent parser for Lua 5.4, building the syntax tree of a chunk.

with Interfaces;
with Pyro.Character_Arrays;
with Pyro.Diagnostics;   use Pyro.Diagnostics;
with Pyro.Lexer;         use Pyro.Lexer;
with Pyro.Parser.Steps;  use Pyro.Parser.Steps;
with Pyro.Tokens;        use Pyro.Tokens;

package body Pyro.Parser with SPARK_Mode => On is

   ------------------------------------------------------------------------------------------
   --  The grammar (lparser.c). Each subprogram mirrors its PUC counterpart, keeps the parser
   --  valid, adds nodes, leaves the list stack as it found it, and returns a node or No_Node.
   --  [proof] Termination: each call either counts a level (the first variant decreases) or
   --  goes to a subprogram of lower rank (the second).

   procedure Statement
     (P : in out Parser_State;
      Source : Sources.Source;
      Level : Nesting_Level;
      Result : out Node_Index)
   with
     Pre                => Valid (P, Source),
     Post               =>
       Kept (P, Source, Node_Count (P.Tree)'Old, Pending (P.Tree)'Old, Limit (P.Budget)'Old)
       and then Result <= Node_Count (P.Tree),
     Subprogram_Variant => (Decreases => Maximum_Level - Level, Decreases => 0);

   procedure Subexpression
     (P : in out Parser_State;
      Source        : Sources.Source;
      Level         : Nesting_Level;
      Limit_Priority : Natural;
      Result        : out Node_Index;
      Next_Operator : out Operator_Kind)
   with
     Pre                => Valid (P, Source),
     Post               =>
       Kept (P, Source, Node_Count (P.Tree)'Old, Pending (P.Tree)'Old, Limit (P.Budget)'Old)
       and then Result <= Node_Count (P.Tree),
     Subprogram_Variant => (Decreases => Maximum_Level - Level, Decreases => 0);

   --  [puc lparser.c:expr]
   procedure Expression
     (P : in out Parser_State;
      Source : Sources.Source;
      Level : Nesting_Level;
      Result : out Node_Index)
   with
     Pre                => Valid (P, Source),
     Post               =>
       Kept (P, Source, Node_Count (P.Tree)'Old, Pending (P.Tree)'Old, Limit (P.Budget)'Old)
       and then Result <= Node_Count (P.Tree),
     Subprogram_Variant => (Decreases => Maximum_Level - Level, Decreases => 1)
   is
      Ignored : Operator_Kind;
   begin
      Subexpression (P, Source, Level, 0, Result, Ignored);
   end Expression;

   --  [puc lparser.c:statlist] Adds the statements to the list being built.
   procedure Statement_List
     (P : in out Parser_State;
      Source : Sources.Source;
      Level : Nesting_Level)
   with
     Pre                => Valid (P, Source),
     Post               =>
       Valid (P, Source)
       and then Node_Count (P.Tree) >= Node_Count (P.Tree)'Old
       and then Pending (P.Tree) >= Pending (P.Tree)'Old
       and then Limit (P.Budget) = Limit (P.Budget)'Old,
     Subprogram_Variant => (Decreases => Maximum_Level - Level, Decreases => 1)
   is
      Item : Node_Index;
   begin
      for Step in 0 .. Source.Length + 1 loop
         exit when P.Failed or else Block_Follow (P, With_Until => True);
         pragma Loop_Invariant (Valid (P, Source));
         pragma Loop_Invariant (Node_Count (P.Tree) >= Node_Count (P.Tree)'Loop_Entry);
         pragma Loop_Invariant (Pending (P.Tree) >= Pending (P.Tree)'Loop_Entry);
         pragma Loop_Invariant (Limit (P.Budget) = Limit (P.Budget)'Loop_Entry);
         if P.Current.Kind = Keyword_Return then
            Statement (P, Source, Level, Item);
            Add_To_List (P, Source, Item);
            exit;
         end if;
         Statement (P, Source, Level, Item);
         Add_To_List (P, Source, Item);
      end loop;
   end Statement_List;

   --  [puc lparser.c:block] A Block node of the statements up to a block-closing token.
   procedure Block_Of
     (P : in out Parser_State;
      Source : Sources.Source;
      Level : Nesting_Level;
      Result : out Node_Index)
   with
     Pre                => Valid (P, Source),
     Post               =>
       Kept (P, Source, Node_Count (P.Tree)'Old, Pending (P.Tree)'Old, Limit (P.Budget)'Old)
       and then Result <= Node_Count (P.Tree),
     Subprogram_Variant => (Decreases => Maximum_Level - Level, Decreases => 2)
   is
      Mark  : constant List_Index := Pending (P.Tree);
      First : constant Source_Position := P.Current.First;
      Line  : constant Line_Number := Pyro.Lexer.Line (P.Lexer);
      Item  : Node;
   begin
      Statement_List (P, Source, Level);
      Item := Shape (P, Block, First, Line);
      Item.Is_Incomplete := P.Failed;
      Make_List (P, Source, Item, Mark, Result);
   end Block_Of;

   --  [puc lparser.c:explist] An Expression_List of one or more expressions.
   procedure Expression_List_Of
     (P : in out Parser_State;
      Source : Sources.Source;
      Level : Nesting_Level;
      Result : out Node_Index)
   with
     Pre                => Valid (P, Source),
     Post               =>
       Kept (P, Source, Node_Count (P.Tree)'Old, Pending (P.Tree)'Old, Limit (P.Budget)'Old)
       and then Result <= Node_Count (P.Tree),
     Subprogram_Variant => (Decreases => Maximum_Level - Level, Decreases => 2)
   is
      Mark  : constant List_Index := Pending (P.Tree);
      First : constant Source_Position := P.Current.First;
      Line  : constant Line_Number := Pyro.Lexer.Line (P.Lexer);
      Item  : Node_Index;
      Found : Boolean;
   begin
      Expression (P, Source, Level, Item);
      Add_To_List (P, Source, Item);
      for Step in 0 .. Source.Length + 1 loop
         pragma Loop_Invariant (Valid (P, Source));
         pragma Loop_Invariant (Node_Count (P.Tree) >= Node_Count (P.Tree)'Loop_Entry);
         pragma Loop_Invariant (Pending (P.Tree) >= Mark);
         pragma Loop_Invariant (Limit (P.Budget) = Limit (P.Budget)'Loop_Entry);
         Test_Next (P, Source, Comma, Found);
         exit when not Found or else P.Failed;
         Expression (P, Source, Level, Item);
         Add_To_List (P, Source, Item);
      end loop;
      Make_List (P, Source, Shape (P, Expression_List, First, Line), Mark, Result);
   end Expression_List_Of;

   --  [puc lparser.c:yindex] '[' expression ']', recovering inside the brackets.
   procedure Index_Key
     (P : in out Parser_State;
      Source : Sources.Source;
      Level : Nesting_Level;
      Result : out Node_Index)
   with
     Pre                => Valid (P, Source),
     Post               =>
       Kept (P, Source, Node_Count (P.Tree)'Old, Pending (P.Tree)'Old, Limit (P.Budget)'Old)
       and then Result <= Node_Count (P.Tree),
     Subprogram_Variant => (Decreases => Maximum_Level - Level, Decreases => 2)
   is
   begin
      Next (P, Source);
      Expression (P, Source, Level, Result);
      if not P.Failed and then P.Current.Kind /= Right_Bracket then
         Error_Expected (P, Source, Right_Bracket);
      end if;
      Recover (P, Source, Left_Bracket);
      Check_Next (P, Source, Right_Bracket);
   end Index_Key;

   --  [puc lparser.c:primaryexp] A name or a parenthesized expression.
   procedure Primary_Expression
     (P : in out Parser_State;
      Source       : Sources.Source;
      Level        : Nesting_Level;
      In_Statement : Boolean;
      Result       : out Node_Index)
   with
     Pre                => Valid (P, Source),
     Post               =>
       Kept (P, Source, Node_Count (P.Tree)'Old, Pending (P.Tree)'Old, Limit (P.Budget)'Old)
       and then Result <= Node_Count (P.Tree),
     Subprogram_Variant => (Decreases => Maximum_Level - Level, Decreases => 2)
   is
      First  : constant Source_Position := P.Current.First;
      Line   : constant Line_Number := Pyro.Lexer.Line (P.Lexer);
      Inner  : Node_Index;
      Symbol : Symbol_Index;
      Item   : Node;
   begin
      Result := No_Node;
      if P.Failed then
         return;
      end if;
      case P.Current.Kind is
         when Left_Parenthesis =>
            declare
               Opener : constant Span := Current_Span (P);
            begin
               Next (P, Source);
               Expression (P, Source, Level, Inner);
               Expect_Closer (P, Source, Right_Parenthesis, Left_Parenthesis, Line, Opener);
               Recover (P, Source, Left_Parenthesis);
               Check_Match (P, Source, Right_Parenthesis, Left_Parenthesis, Line, Opener);
               Item := Shape (P, Parenthesized, First, Line);
               Item.First_Child := Inner;
               Make (P, Source, Item, Result);
            end;
         when Name =>
            Check_Name (P, Source, Symbol);
            Item := Shape (P, Name_Expression, First, Line);
            Item.Symbol := Symbol;
            Make (P, Source, Item, Result);
         when others =>
            Syntax_Error
              (P, Source, (What => Unexpected_Symbol, In_Statement => In_Statement, others => <>));
      end case;
   end Primary_Expression;

   --  [puc lparser.c:recfield] "name = expression", the name at the current token, added to
   --  the list being built.
   procedure Named_Field
     (P : in out Parser_State; Source : Sources.Source; Level : Nesting_Level)
   with
     Pre                => Valid (P, Source),
     Post               =>
       Valid (P, Source)
       and then Node_Count (P.Tree) >= Node_Count (P.Tree)'Old
       and then Pending (P.Tree) >= Pending (P.Tree)'Old
       and then Limit (P.Budget) = Limit (P.Budget)'Old,
     Subprogram_Variant => (Decreases => Maximum_Level - Level, Decreases => 2)
   is
      First  : constant Source_Position := P.Current.First;
      Line   : constant Line_Number := Pyro.Lexer.Line (P.Lexer);
      Item   : Node := Shape (P, String_Literal, First, Line);
      Key    : Node_Index;
      Value  : Node_Index;
      Field  : Node_Index;
      Symbol : Symbol_Index;
   begin
      Check_Name (P, Source, Symbol);
      Item.Symbol := Symbol;
      Item.Last := P.Previous_Last;
      Make (P, Source, Item, Key);
      Check_Next (P, Source, Equals_Sign);
      Expression (P, Source, Level, Value);
      Item := Shape (P, Named_Field, First, Line);
      Item.First_Child := Key;
      Item.Second_Child := Value;
      Item.Is_Name_Key := True;
      Make (P, Source, Item, Field);
      Add_To_List (P, Source, Field);
   end Named_Field;

   --  [puc lparser.c:recfield] "[key] = expression", added to the list being built.
   procedure Bracket_Field
     (P : in out Parser_State; Source : Sources.Source; Level : Nesting_Level)
   with
     Pre                => Valid (P, Source),
     Post               =>
       Valid (P, Source)
       and then Node_Count (P.Tree) >= Node_Count (P.Tree)'Old
       and then Pending (P.Tree) >= Pending (P.Tree)'Old
       and then Limit (P.Budget) = Limit (P.Budget)'Old,
     Subprogram_Variant => (Decreases => Maximum_Level - Level, Decreases => 3)
   is
      First : constant Source_Position := P.Current.First;
      Line  : constant Line_Number := Pyro.Lexer.Line (P.Lexer);
      Item  : Node;
      Key   : Node_Index;
      Value : Node_Index;
      Field : Node_Index;
   begin
      Index_Key (P, Source, Level, Key);
      Check_Next (P, Source, Equals_Sign);
      Expression (P, Source, Level, Value);
      Item := Shape (P, Named_Field, First, Line);
      Item.First_Child := Key;
      Item.Second_Child := Value;
      Make (P, Source, Item, Field);
      Add_To_List (P, Source, Field);
   end Bracket_Field;

   --  [puc lparser.c:field] One field of a table constructor, added to the list being built.
   procedure Table_Field (P : in out Parser_State; Source : Sources.Source; Level : Nesting_Level)
   with
     Pre                => Valid (P, Source),
     Post               =>
       Valid (P, Source)
       and then Node_Count (P.Tree) >= Node_Count (P.Tree)'Old
       and then Pending (P.Tree) >= Pending (P.Tree)'Old
       and then Limit (P.Budget) = Limit (P.Budget)'Old,
     Subprogram_Variant => (Decreases => Maximum_Level - Level, Decreases => 4)
   is
      Value : Node_Index;
   begin
      if P.Current.Kind = Name then
         if not P.Has_Ahead then
            Look_Ahead (P, Source);
         end if;
         if not P.Failed and then P.Has_Ahead and then P.Ahead.Kind = Equals_Sign then
            Named_Field (P, Source, Level);
            return;
         end if;
      elsif P.Current.Kind = Left_Bracket then
         Bracket_Field (P, Source, Level);
         return;
      end if;
      Expression (P, Source, Level, Value);
      Add_To_List (P, Source, Value);
   end Table_Field;

   --  [puc lparser.c:constructor] '{' fields '}', recovering inside the braces.
   procedure Constructor
     (P : in out Parser_State;
      Source : Sources.Source;
      Level : Nesting_Level;
      Result : out Node_Index)
   with
     Pre                => Valid (P, Source),
     Post               =>
       Kept (P, Source, Node_Count (P.Tree)'Old, Pending (P.Tree)'Old, Limit (P.Budget)'Old)
       and then Result <= Node_Count (P.Tree),
     Subprogram_Variant => (Decreases => Maximum_Level - Level, Decreases => 5)
   is
      Mark   : constant List_Index := Pending (P.Tree);
      First  : constant Source_Position := P.Current.First;
      Line   : constant Line_Number := Pyro.Lexer.Line (P.Lexer);
      Opener : constant Span := Current_Span (P);
      Found  : Boolean;
   begin
      Check_Next (P, Source, Left_Brace);
      if not P.Failed then
         for Step in 0 .. Source.Length + 1 loop
            pragma Loop_Invariant (Valid (P, Source));
            pragma Loop_Invariant (Node_Count (P.Tree) >= Node_Count (P.Tree)'Loop_Entry);
            pragma Loop_Invariant (Pending (P.Tree) >= Mark);
            pragma Loop_Invariant (Limit (P.Budget) = Limit (P.Budget)'Loop_Entry);
            exit when P.Failed or else P.Current.Kind = Right_Brace;
            Table_Field (P, Source, Level);
            Test_Next (P, Source, Comma, Found);
            if not Found then
               Test_Next (P, Source, Semicolon, Found);
            end if;
            exit when not Found;
         end loop;
         Expect_Closer (P, Source, Right_Brace, Left_Brace, Line, Opener);
         Recover (P, Source, Left_Brace);
         Check_Match (P, Source, Right_Brace, Left_Brace, Line, Opener);
      end if;
      Make_List (P, Source, Shape (P, Table_Constructor, First, Line), Mark, Result);
   end Constructor;

   --  A Local_Name node for the name at the current token.
   procedure Local_Name_Of
     (P : in out Parser_State; Source : Sources.Source; Result : out Node_Index)
   with
     Pre  => Valid (P, Source),
     Post =>
       Kept (P, Source, Node_Count (P.Tree)'Old, Pending (P.Tree)'Old, Limit (P.Budget)'Old)
       and then Result <= Node_Count (P.Tree)
   is
      Item   : Node := Shape (P, Local_Name, P.Current.First, Pyro.Lexer.Line (P.Lexer));
      Symbol : Symbol_Index;
   begin
      Item.Last := P.Current.Last;
      Check_Name (P, Source, Symbol);
      Item.Symbol := Symbol;
      Make (P, Source, Item, Result);
   end Local_Name_Of;

   --  [puc lparser.c:parlist] '(' parameters ')', as a Name_List, recovering inside the
   --  parentheses. Is_Vararg says the list ends with '...'.
   procedure Parameter_List
     (P         : in out Parser_State;
      Source    : Sources.Source;
      Is_Vararg : out Boolean;
      Result    : out Node_Index)
   with
     Pre  => Valid (P, Source),
     Post =>
       Kept (P, Source, Node_Count (P.Tree)'Old, Pending (P.Tree)'Old, Limit (P.Budget)'Old)
       and then Result <= Node_Count (P.Tree)
   is
      Mark      : constant List_Index := Pending (P.Tree);
      First     : Source_Position;
      Line      : Line_Number;
      Found     : Boolean;
      Parameter : Node_Index;
   begin
      Is_Vararg := False;
      Result := No_Node;
      Check_Next (P, Source, Left_Parenthesis);
      if P.Failed then
         return;
      end if;
      First := P.Current.First;
      Line := Pyro.Lexer.Line (P.Lexer);
      if P.Current.Kind /= Right_Parenthesis then
         for Step in 0 .. Source.Length + 1 loop
            pragma Loop_Invariant (Valid (P, Source));
            pragma Loop_Invariant (Node_Count (P.Tree) >= Node_Count (P.Tree)'Loop_Entry);
            pragma Loop_Invariant (Pending (P.Tree) >= Mark);
            pragma Loop_Invariant (Limit (P.Budget) = Limit (P.Budget)'Loop_Entry);
            exit when P.Failed;
            if P.Current.Kind = Name then
               Local_Name_Of (P, Source, Parameter);
               Add_To_List (P, Source, Parameter);
            elsif P.Current.Kind = Triple_Dot then
               Next (P, Source);
               Is_Vararg := True;
            else
               Syntax_Error (P, Source, (What => Name_Or_Vararg_Expected, others => <>));
            end if;
            exit when Is_Vararg;
            Test_Next (P, Source, Comma, Found);
            exit when not Found;
         end loop;
      end if;
      if not P.Failed and then P.Current.Kind /= Right_Parenthesis then
         Error_Expected (P, Source, Right_Parenthesis);
      end if;
      Recover (P, Source, Left_Parenthesis);
      Make_List (P, Source, Shape (P, Name_List, First, Line), Mark, Result);
      Check_Next (P, Source, Right_Parenthesis);
   end Parameter_List;

   --  [puc lparser.c:body] '(' parameters ')' block 'end'. Line is where the function starts.
   procedure Function_Body_Of
     (P         : in out Parser_State;
      Source    : Sources.Source;
      Level     : Nesting_Level;
      Is_Method : Boolean;
      Line      : Line_Number;
      Opener    : Span;
      Result    : out Node_Index)
   with
     Pre                => Valid (P, Source),
     Post               =>
       Kept (P, Source, Node_Count (P.Tree)'Old, Pending (P.Tree)'Old, Limit (P.Budget)'Old)
       and then Result <= Node_Count (P.Tree)
       and then P.In_Vararg = P.In_Vararg'Old,
     Subprogram_Variant => (Decreases => Maximum_Level - Level, Decreases => 3)
   is
      Outer_Vararg : constant Boolean := P.In_Vararg;
      First        : constant Source_Position := P.Current.First;
      Parameters   : Node_Index;
      Statements   : Node_Index;
      Item         : Node;
      Is_Vararg    : Boolean;
   begin
      Parameter_List (P, Source, Is_Vararg, Parameters);
      Set_Vararg (P, Source, Is_Vararg);
      Block_Of (P, Source, Level, Statements);
      Check_Match (P, Source, Keyword_End, Keyword_Function, Line, Opener);
      Item := Shape (P, Function_Body, First, Line);
      Item.First_Child := Parameters;
      Item.Second_Child := Statements;
      Item.Is_Vararg := Is_Vararg;
      Item.Is_Method := Is_Method;
      Item.Is_Incomplete := P.Failed;
      --  [puc lparser.c:close_func] Pending gotos are checked looking at the token after 'end'.
      Item.Check_Point := (Ordinal => P.Current.Ordinal, During => Resolving);
      Item.Check_Line := Pyro.Lexer.Line (P.Lexer);
      Make (P, Source, Item, Result);
      Set_Vararg (P, Source, Outer_Vararg);
   end Function_Body_Of;

   --  [puc lparser.c:funcargs] '(' [expressions] ')', recovering inside the parentheses. Adds
   --  the arguments to the list being built.
   procedure Parenthesized_Arguments
     (P : in out Parser_State; Source : Sources.Source; Level : Nesting_Level)
   with
     Pre                => Valid (P, Source),
     Post               =>
       Valid (P, Source)
       and then Node_Count (P.Tree) >= Node_Count (P.Tree)'Old
       and then Pending (P.Tree) >= Pending (P.Tree)'Old
       and then Limit (P.Budget) = Limit (P.Budget)'Old,
     Subprogram_Variant => (Decreases => Maximum_Level - Level, Decreases => 2)
   is
      Line   : constant Line_Number := Pyro.Lexer.Line (P.Lexer);
      Opener : constant Span := Current_Span (P);
      Item   : Node_Index;
      Found  : Boolean;
   begin
      Next (P, Source);
      if not P.Failed and then P.Current.Kind /= Right_Parenthesis then
         for Step in 0 .. Source.Length + 1 loop
            pragma Loop_Invariant (Valid (P, Source));
            pragma Loop_Invariant (Node_Count (P.Tree) >= Node_Count (P.Tree)'Loop_Entry);
            pragma Loop_Invariant (Pending (P.Tree) >= Pending (P.Tree)'Loop_Entry);
            pragma Loop_Invariant (Limit (P.Budget) = Limit (P.Budget)'Loop_Entry);
            Expression (P, Source, Level, Item);
            Add_To_List (P, Source, Item);
            Test_Next (P, Source, Comma, Found);
            exit when not Found;
         end loop;
      end if;
      Expect_Closer (P, Source, Right_Parenthesis, Left_Parenthesis, Line, Opener);
      Recover (P, Source, Left_Parenthesis);
      Check_Match (P, Source, Right_Parenthesis, Left_Parenthesis, Line, Opener);
   end Parenthesized_Arguments;

   --  [puc lparser.c:funcargs] Call arguments: '(' expressions ')', a table or a string. Adds
   --  the arguments to the list being built.
   procedure Function_Arguments
     (P : in out Parser_State; Source : Sources.Source; Level : Nesting_Level)
   with
     Pre                => Valid (P, Source),
     Post               =>
       Valid (P, Source)
       and then Node_Count (P.Tree) >= Node_Count (P.Tree)'Old
       and then Pending (P.Tree) >= Pending (P.Tree)'Old
       and then Limit (P.Budget) = Limit (P.Budget)'Old,
     Subprogram_Variant => (Decreases => Maximum_Level - Level, Decreases => 6)
   is
      Item : Node_Index;
      Text : Node;
   begin
      if P.Failed then
         return;
      end if;
      case P.Current.Kind is
         when Left_Parenthesis =>
            Parenthesized_Arguments (P, Source, Level);
         when Left_Brace =>
            Constructor (P, Source, Level, Item);
            Add_To_List (P, Source, Item);
         when String_Literal =>
            Text := Shape (P, String_Literal, P.Current.First, Pyro.Lexer.Line (P.Lexer));
            Text.Last := P.Current.Last;
            Text.Symbol := P.Current.Symbol;
            Next (P, Source);
            Make (P, Source, Text, Item);
            Add_To_List (P, Source, Item);
         when others =>
            Syntax_Error (P, Source, (What => Function_Arguments_Expected, others => <>));
      end case;
   end Function_Arguments;

   --  [puc lparser.c:suffixedexp] A primary expression followed by fields, indexes, method
   --  calls and calls.
   procedure Suffixed_Expression
     (P : in out Parser_State;
      Source       : Sources.Source;
      Level        : Nesting_Level;
      In_Statement : Boolean;
      Result       : out Node_Index)
   with
     Pre                => Valid (P, Source),
     Post               =>
       Kept (P, Source, Node_Count (P.Tree)'Old, Pending (P.Tree)'Old, Limit (P.Budget)'Old)
       and then Result <= Node_Count (P.Tree),
     Subprogram_Variant => (Decreases => Maximum_Level - Level, Decreases => 7)
   is
      First  : constant Source_Position := P.Current.First;
      Item   : Node;
      Key    : Node_Index;
      Line   : Line_Number;
      Mark   : List_Index;
      Symbol : Symbol_Index;
   begin
      Primary_Expression (P, Source, Level, In_Statement, Result);
      for Step in 0 .. Source.Length + 1 loop
         pragma Loop_Invariant
           (Kept (P, Source, Node_Count (P.Tree)'Loop_Entry, Pending (P.Tree)'Loop_Entry,
                  Limit (P.Budget)'Loop_Entry));
         pragma Loop_Invariant (Result <= Node_Count (P.Tree));
         exit when P.Failed;
         Line := Pyro.Lexer.Line (P.Lexer);
         case P.Current.Kind is
            when Dot =>
               --  [puc lparser.c:fieldsel]
               Next (P, Source);
               Item := Shape (P, String_Literal, P.Current.First, Line);
               Item.Last := P.Current.Last;
               Check_Name (P, Source, Symbol);
               Item.Symbol := Symbol;
               Make (P, Source, Item, Key);
               Item := Shape (P, Index_Expression, First, Line);
               Item.First_Child := Result;
               Item.Second_Child := Key;
               Item.Is_Name_Key := True;
               Make (P, Source, Item, Result);
            when Left_Bracket =>
               Index_Key (P, Source, Level, Key);
               Item := Shape (P, Index_Expression, First, Line);
               Item.First_Child := Result;
               Item.Second_Child := Key;
               Make (P, Source, Item, Result);
            when Colon =>
               Next (P, Source);
               Check_Name (P, Source, Symbol);
               Mark := Pending (P.Tree);
               Function_Arguments (P, Source, Level);
               Item := Shape (P, Method_Call, First, Line);
               Item.First_Child := Result;
               Item.Symbol := Symbol;
               Make_List (P, Source, Item, Mark, Result);
            when Left_Parenthesis | String_Literal | Left_Brace =>
               Mark := Pending (P.Tree);
               Function_Arguments (P, Source, Level);
               Item := Shape (P, Call_Expression, First, Line);
               Item.First_Child := Result;
               Make_List (P, Source, Item, Mark, Result);
            when others =>
               exit;
         end case;
      end loop;
   end Suffixed_Expression;

   --  [puc lparser.c:simpleexp]
   procedure Simple_Expression
     (P : in out Parser_State;
      Source : Sources.Source;
      Level : Nesting_Level;
      Result : out Node_Index)
   with
     Pre                => Valid (P, Source),
     Post               =>
       Kept (P, Source, Node_Count (P.Tree)'Old, Pending (P.Tree)'Old, Limit (P.Budget)'Old)
       and then Result <= Node_Count (P.Tree),
     Subprogram_Variant => (Decreases => Maximum_Level - Level, Decreases => 8)
   is
      First : constant Source_Position := P.Current.First;
      Line  : constant Line_Number := Pyro.Lexer.Line (P.Lexer);
      Item  : Node := Shape (P, Missing, First, Line);
      Inner : Node_Index;
   begin
      Result := No_Node;
      if P.Failed then
         return;
      end if;
      Item.Last := P.Current.Last;
      case P.Current.Kind is
         when Float_Numeral =>
            Item.Kind := Float_Literal;
            Item.Value := P.Current.Float_Bits;
         when Integer_Numeral =>
            Item.Kind := Integer_Literal;
            Item.Value := Interfaces.Unsigned_64'Mod (P.Current.Integer_Value);
         when String_Literal =>
            Item.Kind := String_Literal;
            Item.Symbol := P.Current.Symbol;
         when Keyword_Nil =>
            Item.Kind := Nil_Literal;
         when Keyword_True =>
            Item.Kind := True_Literal;
         when Keyword_False =>
            Item.Kind := False_Literal;
         when Triple_Dot =>
            Item.Kind := Vararg_Expression;
            if not P.In_Vararg then
               --  [puc lparser.c:simpleexp] A luaX_syntaxerror in PUC Lua, so it has "near"
               --  text; reported without stopping (DESIGN.md, Diagnostics).
               declare
                  Problem_Record : constant Diagnostic :=
                    (What => Vararg_Outside_Vararg_Function, others => <>);
               begin
                  Report_Current (P, Source, Problem_Record, Near => True);
               end;
            end if;
         when Left_Brace =>
            Constructor (P, Source, Level, Result);
            return;
         when Keyword_Function =>
            declare
               Opener : constant Span := Current_Span (P);
            begin
               Next (P, Source);
               Function_Body_Of
                 (P, Source, Level, False, Pyro.Lexer.Line (P.Lexer), Opener, Inner);
               Item := Shape (P, Function_Expression, First, Line);
               Item.First_Child := Inner;
               Make (P, Source, Item, Result);
            end;
            return;
         when others =>
            Suffixed_Expression (P, Source, Level, False, Result);
            return;
      end case;
      Next (P, Source);
      Make (P, Source, Item, Result);
   end Simple_Expression;

   --  [puc lparser.c:getunopr]
   function Unary_Operator (Kind : Token_Kind) return Operator_Kind
   is (case Kind is
         when Keyword_Not  => Logical_Not,
         when Minus_Sign   => Negate,
         when Tilde        => Bitwise_Not,
         when Number_Sign  => Length,
         when others       => No_Operator);

   --  [puc lparser.c:getbinopr]
   function Binary_Operator (Kind : Token_Kind) return Operator_Kind
   is (case Kind is
         when Plus_Sign     => Add,
         when Minus_Sign    => Subtract,
         when Asterisk      => Multiply,
         when Percent_Sign  => Modulo,
         when Caret         => Power,
         when Slash         => Divide,
         when Double_Slash  => Floor_Divide,
         when Ampersand     => Bitwise_And,
         when Vertical_Bar  => Bitwise_Or,
         when Tilde         => Bitwise_Exclusive_Or,
         when Shift_Left    => Shift_Left,
         when Shift_Right   => Shift_Right,
         when Double_Dot    => Concatenate,
         when Not_Equal     => Not_Equal,
         when Equal_Equal   => Equal,
         when Less_Than     => Less,
         when Less_Equal    => Less_Equal,
         when Greater_Than  => Greater,
         when Greater_Equal => Greater_Equal,
         when Keyword_And   => And_Then,
         when Keyword_Or    => Or_Else,
         when others        => No_Operator);

   --  [puc lparser.c:priority] Left and right priorities of the binary operators.
   function Left_Priority (Operator : Operator_Kind) return Natural
   is (case Operator is
         when Add | Subtract => 10,
         when Multiply | Modulo | Divide | Floor_Divide => 11,
         when Power => 14,
         when Bitwise_And => 6,
         when Bitwise_Or => 4,
         when Bitwise_Exclusive_Or => 5,
         when Shift_Left | Shift_Right => 7,
         when Concatenate => 9,
         when Equal | Not_Equal | Less | Less_Equal | Greater | Greater_Equal => 3,
         when And_Then => 2,
         when Or_Else => 1,
         when others => 0);

   function Right_Priority (Operator : Operator_Kind) return Natural
   is (case Operator is
         when Power => 13,
         when Concatenate => 8,
         when others => Left_Priority (Operator));

   --  [puc lparser.c:UNARY_PRIORITY]
   Unary_Priority : constant := 12;

   procedure Subexpression
     (P : in out Parser_State;
      Source        : Sources.Source;
      Level         : Nesting_Level;
      Limit_Priority : Natural;
      Result        : out Node_Index;
      Next_Operator : out Operator_Kind)
   is
      First    : constant Source_Position := P.Current.First;
      Overflow : Boolean;
      Item     : Node;
      Operand  : Node_Index;
      Right    : Node_Index;
      Operator : Operator_Kind;
      Following : Operator_Kind;
      Line     : Line_Number;
   begin
      Result := No_Node;
      Next_Operator := No_Operator;
      Enter_Level (P, Source, Level, Overflow);
      if Overflow or else P.Failed then
         return;
      end if;
      Operator := Unary_Operator (P.Current.Kind);
      if Operator /= No_Operator then
         Line := Pyro.Lexer.Line (P.Lexer);
         Next (P, Source);
         Subexpression (P, Source, Level + 1, Unary_Priority, Operand, Following);
         Item := Shape (P, Unary_Operation, First, Line);
         Item.Operator := Operator;
         Item.First_Child := Operand;
         Make (P, Source, Item, Result);
         --  The operator after the operand, which PUC reads again from the current token.
         Operator := (if P.Failed then No_Operator else Following);
      else
         Simple_Expression (P, Source, Level + 1, Result);
         Operator := (if P.Failed then No_Operator else Binary_Operator (P.Current.Kind));
      end if;
      for Step in 0 .. Source.Length + 1 loop
         exit when Operator = No_Operator or else Left_Priority (Operator) <= Limit_Priority;
         pragma Loop_Invariant
           (Kept (P, Source, Node_Count (P.Tree)'Loop_Entry, Pending (P.Tree)'Loop_Entry,
                  Limit (P.Budget)'Loop_Entry));
         pragma Loop_Invariant (Result <= Node_Count (P.Tree));
         Line := Pyro.Lexer.Line (P.Lexer);
         Next (P, Source);
         Subexpression (P, Source, Level + 1, Right_Priority (Operator), Right, Following);
         Item := Shape (P, Binary_Operation, First, Line);
         Item.Operator := Operator;
         Item.First_Child := Result;
         Item.Second_Child := Right;
         Make (P, Source, Item, Result);
         Operator := (if P.Failed then No_Operator else Following);
      end loop;
      Next_Operator := Operator;
   end Subexpression;

   --  [puc lparser.c:test_then_block] An If_Clause: condition 'then' statements.
   procedure Test_Then_Block
     (P : in out Parser_State;
      Source : Sources.Source;
      Level : Nesting_Level;
      Result : out Node_Index)
   with
     Pre                => Valid (P, Source),
     Post               =>
       Kept (P, Source, Node_Count (P.Tree)'Old, Pending (P.Tree)'Old, Limit (P.Budget)'Old)
       and then Result <= Node_Count (P.Tree),
     Subprogram_Variant => (Decreases => Maximum_Level - Level, Decreases => 2)
   is
      First     : constant Source_Position := P.Current.First;
      Line      : constant Line_Number := Pyro.Lexer.Line (P.Lexer);
      Condition : Node_Index;
      Mark      : List_Index;
      Body_First : Source_Position;
      Body_Line : Line_Number;
      Item      : Node;
      Statements : Node_Index;
      Break_Node : Node_Index;
      Found     : Boolean;
   begin
      Next (P, Source);
      Expression (P, Source, Level, Condition);
      Check_Next (P, Source, Keyword_Then);
      Mark := Pending (P.Tree);
      Body_First := P.Current.First;
      Body_Line := Pyro.Lexer.Line (P.Lexer);
      if not P.Failed and then P.Current.Kind = Keyword_Break then
         --  'if x then break': the break is read here, then ';'s are skipped without
         --  counting levels, as PUC does.
         Item := Shape (P, Break_Statement, P.Current.First, Pyro.Lexer.Line (P.Lexer));
         Item.Last := P.Current.Last;
         Next (P, Source);
         Make (P, Source, Item, Break_Node);
         Add_To_List (P, Source, Break_Node);
         for Step in 0 .. Source.Length + 1 loop
            pragma Loop_Invariant (Valid (P, Source));
            pragma Loop_Invariant (Node_Count (P.Tree) >= Node_Count (P.Tree)'Loop_Entry);
            pragma Loop_Invariant (Pending (P.Tree) >= Mark);
            pragma Loop_Invariant (Limit (P.Budget) = Limit (P.Budget)'Loop_Entry);
            Test_Next (P, Source, Semicolon, Found);
            exit when not Found;
         end loop;
         if not P.Failed and then not Block_Follow (P, With_Until => False) then
            Statement_List (P, Source, Level);
         end if;
      else
         Statement_List (P, Source, Level);
      end if;
      Item := Shape (P, Block, Body_First, Body_Line);
      Item.Is_Incomplete := P.Failed;
      Make_List (P, Source, Item, Mark, Statements);
      Item := Shape (P, If_Clause, First, Line);
      Item.First_Child := Condition;
      Item.Second_Child := Statements;
      Make (P, Source, Item, Result);
   end Test_Then_Block;

   --  [puc lparser.c:ifstat]
   procedure If_Statement
     (P : in out Parser_State;
      Source : Sources.Source;
      Level  : Nesting_Level;
      Line   : Line_Number;
      Result : out Node_Index)
   with
     Pre                => Valid (P, Source),
     Post               =>
       Kept (P, Source, Node_Count (P.Tree)'Old, Pending (P.Tree)'Old, Limit (P.Budget)'Old)
       and then Result <= Node_Count (P.Tree),
     Subprogram_Variant => (Decreases => Maximum_Level - Level, Decreases => 3)
   is
      Mark   : constant List_Index := Pending (P.Tree);
      First  : constant Source_Position := P.Current.First;
      Opener : constant Span := Current_Span (P);
      Clause : Node_Index;
      Others_Block : Node_Index := No_Node;
      Found  : Boolean;
      Item   : Node;
   begin
      Test_Then_Block (P, Source, Level, Clause);
      Add_To_List (P, Source, Clause);
      for Step in 0 .. Source.Length + 1 loop
         exit when P.Failed or else P.Current.Kind /= Keyword_Elseif;
         pragma Loop_Invariant (Valid (P, Source));
         pragma Loop_Invariant (Node_Count (P.Tree) >= Node_Count (P.Tree)'Loop_Entry);
         pragma Loop_Invariant (Pending (P.Tree) >= Mark);
         pragma Loop_Invariant (Limit (P.Budget) = Limit (P.Budget)'Loop_Entry);
         Test_Then_Block (P, Source, Level, Clause);
         Add_To_List (P, Source, Clause);
      end loop;
      Test_Next (P, Source, Keyword_Else, Found);
      if Found then
         Block_Of (P, Source, Level, Others_Block);
      end if;
      Check_Match (P, Source, Keyword_End, Keyword_If, Line, Opener);
      Item := Shape (P, If_Statement, First, Line);
      Item.First_Child := Others_Block;
      Make_List (P, Source, Item, Mark, Result);
   end If_Statement;

   --  [puc lparser.c:whilestat]
   procedure While_Statement
     (P : in out Parser_State;
      Source : Sources.Source;
      Level  : Nesting_Level;
      Line   : Line_Number;
      Result : out Node_Index)
   with
     Pre                => Valid (P, Source),
     Post               =>
       Kept (P, Source, Node_Count (P.Tree)'Old, Pending (P.Tree)'Old, Limit (P.Budget)'Old)
       and then Result <= Node_Count (P.Tree),
     Subprogram_Variant => (Decreases => Maximum_Level - Level, Decreases => 3)
   is
      First     : constant Source_Position := P.Current.First;
      Opener    : constant Span := Current_Span (P);
      Condition : Node_Index;
      Statements : Node_Index;
      Item      : Node;
   begin
      Next (P, Source);
      Expression (P, Source, Level, Condition);
      Check_Next (P, Source, Keyword_Do);
      Block_Of (P, Source, Level, Statements);
      Check_Match (P, Source, Keyword_End, Keyword_While, Line, Opener);
      Item := Shape (P, While_Statement, First, Line);
      Item.First_Child := Condition;
      Item.Second_Child := Statements;
      Make (P, Source, Item, Result);
   end While_Statement;

   --  [puc lparser.c:repeatstat]
   procedure Repeat_Statement
     (P : in out Parser_State;
      Source : Sources.Source;
      Level  : Nesting_Level;
      Line   : Line_Number;
      Result : out Node_Index)
   with
     Pre                => Valid (P, Source),
     Post               =>
       Kept (P, Source, Node_Count (P.Tree)'Old, Pending (P.Tree)'Old, Limit (P.Budget)'Old)
       and then Result <= Node_Count (P.Tree),
     Subprogram_Variant => (Decreases => Maximum_Level - Level, Decreases => 2)
   is
      First      : constant Source_Position := P.Current.First;
      Opener     : constant Span := Current_Span (P);
      Mark       : constant List_Index := Pending (P.Tree);
      Statements : Node_Index;
      Condition  : Node_Index := No_Node;
      Item       : Node;
      Body_First : Source_Position;
      Body_Line  : Line_Number;
   begin
      Next (P, Source);
      Body_First := P.Current.First;
      Body_Line := Pyro.Lexer.Line (P.Lexer);
      Statement_List (P, Source, Level);
      Item := Shape (P, Block, Body_First, Body_Line);
      Item.Is_Incomplete := P.Failed;
      Make_List (P, Source, Item, Mark, Statements);
      Check_Match (P, Source, Keyword_Until, Keyword_Repeat, Line, Opener);
      if not P.Failed then
         Expression (P, Source, Level, Condition);
      end if;
      Item := Shape (P, Repeat_Statement, First, Line);
      Item.First_Child := Statements;
      Item.Second_Child := Condition;
      Make (P, Source, Item, Result);
   end Repeat_Statement;

   --  [puc lparser.c:fornum] '=' start ',' limit [',' step], as an Expression_List.
   procedure Numeric_For_Values
     (P : in out Parser_State; Source : Sources.Source; Level : Nesting_Level;
      Result : out Node_Index)
   with
     Pre                => Valid (P, Source),
     Post               =>
       Kept (P, Source, Node_Count (P.Tree)'Old, Pending (P.Tree)'Old, Limit (P.Budget)'Old)
       and then Result <= Node_Count (P.Tree),
     Subprogram_Variant => (Decreases => Maximum_Level - Level, Decreases => 2)
   is
      Mark  : constant List_Index := Pending (P.Tree);
      First : Source_Position;
      Line  : Line_Number;
      Value : Node_Index;
      Found : Boolean;
   begin
      Next (P, Source);
      First := P.Current.First;
      Line := Pyro.Lexer.Line (P.Lexer);
      Expression (P, Source, Level, Value);
      Add_To_List (P, Source, Value);
      Check_Next (P, Source, Comma);
      Expression (P, Source, Level, Value);
      Add_To_List (P, Source, Value);
      Test_Next (P, Source, Comma, Found);
      if Found then
         Expression (P, Source, Level, Value);
         Add_To_List (P, Source, Value);
      end if;
      Make_List (P, Source, Shape (P, Expression_List, First, Line), Mark, Result);
   end Numeric_For_Values;

   --  [puc lparser.c:forlist] The names of a generic 'for', the first (Variable) already read,
   --  as a Name_List.
   procedure Generic_For_Names
     (P        : in out Parser_State;
      Source   : Sources.Source;
      First    : Source_Position;
      Line     : Line_Number;
      Variable : Node_Index;
      Result   : out Node_Index)
   with
     Pre  => Valid (P, Source) and then Variable <= Node_Count (P.Tree),
     Post =>
       Kept (P, Source, Node_Count (P.Tree)'Old, Pending (P.Tree)'Old, Limit (P.Budget)'Old)
       and then Result <= Node_Count (P.Tree)
   is
      Mark  : constant List_Index := Pending (P.Tree);
      Name  : Node_Index;
      Found : Boolean;
   begin
      Add_To_List (P, Source, Variable);
      for Step in 0 .. Source.Length + 1 loop
         pragma Loop_Invariant (Valid (P, Source));
         pragma Loop_Invariant (Node_Count (P.Tree) >= Node_Count (P.Tree)'Loop_Entry);
         pragma Loop_Invariant (Pending (P.Tree) >= Mark);
         pragma Loop_Invariant (Limit (P.Budget) = Limit (P.Budget)'Loop_Entry);
         Test_Next (P, Source, Comma, Found);
         exit when not Found;
         Local_Name_Of (P, Source, Name);
         Add_To_List (P, Source, Name);
      end loop;
      Make_List (P, Source, Shape (P, Name_List, First, Line), Mark, Result);
   end Generic_For_Names;

   --  [puc lparser.c:forstat] Numeric and generic 'for'.
   procedure For_Statement
     (P      : in out Parser_State;
      Source : Sources.Source;
      Level  : Nesting_Level;
      Line   : Line_Number;
      Result : out Node_Index)
   with
     Pre                => Valid (P, Source),
     Post               =>
       Kept (P, Source, Node_Count (P.Tree)'Old, Pending (P.Tree)'Old, Limit (P.Budget)'Old)
       and then Result <= Node_Count (P.Tree),
     Subprogram_Variant => (Decreases => Maximum_Level - Level, Decreases => 3)
   is
      First      : constant Source_Position := P.Current.First;
      Opener     : constant Span := Current_Span (P);
      Variables  : Node_Index := No_Node;
      Values     : Node_Index := No_Node;
      Statements : Node_Index := No_Node;
      Variable   : Node_Index;
      Item       : Node;
      Kind       : Node_Kind := Numeric_For;
   begin
      Next (P, Source);
      Local_Name_Of (P, Source, Variable);
      if not P.Failed and then P.Current.Kind = Equals_Sign then
         Variables := Variable;
         Numeric_For_Values (P, Source, Level, Values);
      elsif not P.Failed and then P.Current.Kind in Comma | Keyword_In then
         Kind := Generic_For;
         Generic_For_Names (P, Source, First, Line, Variable, Variables);
         Check_Next (P, Source, Keyword_In);
         Expression_List_Of (P, Source, Level, Values);
      elsif not P.Failed then
         Syntax_Error (P, Source, (What => Equals_Or_In_Expected, others => <>));
      end if;
      --  [puc lparser.c:forbody]
      Check_Next (P, Source, Keyword_Do);
      if not P.Failed then
         Block_Of (P, Source, Level, Statements);
      end if;
      Check_Match (P, Source, Keyword_End, Keyword_For, Line, Opener);
      Item := Shape (P, Kind, First, Line);
      Item.First_Child := Variables;
      Item.Second_Child := Values;
      Item.Third_Child := Statements;
      Make (P, Source, Item, Result);
   end For_Statement;

   --  [puc lparser.c:funcname] name {'.' name} [':' name], as a name or index expression.
   procedure Function_Name
     (P         : in out Parser_State;
      Source    : Sources.Source;
      Is_Method : out Boolean;
      Result    : out Node_Index)
   with
     Pre  => Valid (P, Source),
     Post =>
       Kept (P, Source, Node_Count (P.Tree)'Old, Pending (P.Tree)'Old, Limit (P.Budget)'Old)
       and then Result <= Node_Count (P.Tree)
   is
      Name_First : constant Source_Position := P.Current.First;
      Item       : Node := Shape (P, Name_Expression, Name_First, Pyro.Lexer.Line (P.Lexer));
      Key        : Node_Index;
      Symbol     : Symbol_Index;
   begin
      Is_Method := False;
      Check_Name (P, Source, Symbol);
      Item.Symbol := Symbol;
      Item.Last := P.Previous_Last;
      Make (P, Source, Item, Result);
      for Step in 0 .. Source.Length + 1 loop
         pragma Loop_Invariant
           (Kept (P, Source, Node_Count (P.Tree)'Loop_Entry, Pending (P.Tree)'Loop_Entry,
                  Limit (P.Budget)'Loop_Entry));
         pragma Loop_Invariant (Result <= Node_Count (P.Tree));
         exit when P.Failed or else P.Current.Kind not in Dot | Colon or else Is_Method;
         Is_Method := P.Current.Kind = Colon;
         Next (P, Source);
         Item := Shape (P, String_Literal, P.Current.First, Pyro.Lexer.Line (P.Lexer));
         Item.Last := P.Current.Last;
         Check_Name (P, Source, Symbol);
         Item.Symbol := Symbol;
         Make (P, Source, Item, Key);
         Item := Shape (P, Index_Expression, Name_First, Pyro.Lexer.Line (P.Lexer));
         Item.First_Child := Result;
         Item.Second_Child := Key;
         Item.Is_Name_Key := True;
         Make (P, Source, Item, Result);
      end loop;
   end Function_Name;

   --  [puc lparser.c:funcstat] 'function' name {'.' name} [':' name] body
   procedure Function_Statement
     (P : in out Parser_State;
      Source : Sources.Source;
      Level  : Nesting_Level;
      Line   : Line_Number;
      Result : out Node_Index)
   with
     Pre                => Valid (P, Source),
     Post               =>
       Kept (P, Source, Node_Count (P.Tree)'Old, Pending (P.Tree)'Old, Limit (P.Budget)'Old)
       and then Result <= Node_Count (P.Tree),
     Subprogram_Variant => (Decreases => Maximum_Level - Level, Decreases => 4)
   is
      First     : constant Source_Position := P.Current.First;
      Opener    : constant Span := Current_Span (P);
      Target    : Node_Index;
      Body_Node : Node_Index;
      Item      : Node;
      Is_Method : Boolean;
   begin
      Next (P, Source);
      Function_Name (P, Source, Is_Method, Target);
      Function_Body_Of (P, Source, Level, Is_Method, Line, Opener, Body_Node);
      Item := Shape (P, Function_Statement, First, Line);
      Item.First_Child := Target;
      Item.Second_Child := Body_Node;
      Item.Is_Method := Is_Method;
      --  [puc lparser.c:funcstat] check_readonly comes after the body.
      Item.Check_Point := (Ordinal => P.Current.Ordinal, During => Resolving);
      Item.Check_Line := Pyro.Lexer.Line (P.Lexer);
      Make (P, Source, Item, Result);
   end Function_Statement;

   --  [puc lparser.c:localfunc] 'local' 'function' name body
   procedure Local_Function
     (P : in out Parser_State;
      Source : Sources.Source;
      Level  : Nesting_Level;
      First  : Source_Position;
      Line   : Line_Number;
      Opener : Span;
      Result : out Node_Index)
   with
     Pre                => Valid (P, Source),
     Post               =>
       Kept (P, Source, Node_Count (P.Tree)'Old, Pending (P.Tree)'Old, Limit (P.Budget)'Old)
       and then Result <= Node_Count (P.Tree),
     Subprogram_Variant => (Decreases => Maximum_Level - Level, Decreases => 4)
   is
      Name_Node : Node_Index;
      Body_Node : Node_Index;
      Item      : Node;
      Symbol    : Symbol_Index;
   begin
      Item := Shape (P, Local_Name, P.Current.First, Pyro.Lexer.Line (P.Lexer));
      Item.Last := P.Current.Last;
      Check_Name (P, Source, Symbol);
      Item.Symbol := Symbol;
      Make (P, Source, Item, Name_Node);
      Function_Body_Of (P, Source, Level, False, Pyro.Lexer.Line (P.Lexer), Opener, Body_Node);
      Item := Shape (P, Local_Function, First, Line);
      Item.First_Child := Name_Node;
      Item.Second_Child := Body_Node;
      Make (P, Source, Item, Result);
   end Local_Function;

   --  [puc lparser.c:localstat, getlocalattribute] One "name [<attribute>]" of a local
   --  declaration, as a Local_Name. Closing says a <close> variable came before (at
   --  First_Close); a second one is an error.
   procedure Local_Variable
     (P           : in out Parser_State;
      Source      : Sources.Source;
      Closing     : in out Boolean;
      First_Close : in out Span;
      Result      : out Node_Index)
   with
     Pre  => Valid (P, Source),
     Post =>
       Kept (P, Source, Node_Count (P.Tree)'Old, Pending (P.Tree)'Old, Limit (P.Budget)'Old)
       and then Result <= Node_Count (P.Tree)
   is
      Item      : Node := Shape (P, Local_Name, P.Current.First, Pyro.Lexer.Line (P.Lexer));
      Symbol    : Symbol_Index;
      Attribute : Symbol_Index;
      Found     : Boolean;
      Attribute_Span : Span;
   begin
      Item.Last := P.Current.Last;
      Check_Name (P, Source, Symbol);
      Item.Symbol := Symbol;
      Test_Next (P, Source, Less_Than, Found);
      if Found then
         Attribute_Span := Current_Span (P);
         Check_Name (P, Source, Attribute);
         Check_Next (P, Source, Greater_Than);
         if P.Failed then
            null;
         elsif Is_Attribute (P, Source, Attribute, "const") then
            Item.Attribute := Constant_Attribute;
         elsif Is_Attribute (P, Source, Attribute, "close") then
            Item.Attribute := Close_Attribute;
            if Closing then
               Report_Current
                 (P, Source,
                  (What       => Multiple_To_Be_Closed,
                   Name       => Symbol,
                   Links      => 1,
                   First_Link => First_Close,
                   Has_Place  => True,
                   Place      => (First => Item.First, Last => Item.Last),
                   others     => <>),
                  Near => False);
            else
               Closing := True;
               First_Close := (First => Item.First, Last => Item.Last);
            end if;
         else
            Report_Current
              (P, Source,
               (What      => Unknown_Attribute,
                Name      => Attribute,
                Has_Place => True,
                Place     => Attribute_Span,
                others    => <>),
               Near => False);
         end if;
      end if;
      Make (P, Source, Item, Result);
   end Local_Variable;

   --  [puc lparser.c:localstat] 'local' name attribute {',' name attribute} ['=' explist]
   procedure Local_Statement
     (P      : in out Parser_State;
      Source : Sources.Source;
      Level  : Nesting_Level;
      First  : Source_Position;
      Line   : Line_Number;
      Result : out Node_Index)
   with
     Pre                => Valid (P, Source),
     Post               =>
       Kept (P, Source, Node_Count (P.Tree)'Old, Pending (P.Tree)'Old, Limit (P.Budget)'Old)
       and then Result <= Node_Count (P.Tree),
     Subprogram_Variant => (Decreases => Maximum_Level - Level, Decreases => 3)
   is
      Mark        : constant List_Index := Pending (P.Tree);
      Names_First : constant Source_Position := P.Current.First;
      Names_Line  : constant Line_Number := Pyro.Lexer.Line (P.Lexer);
      Names       : Node_Index;
      Values      : Node_Index := No_Node;
      Variable    : Node_Index;
      Item        : Node;
      Found       : Boolean;
      Closing     : Boolean := False;
      First_Close : Span := (First => 1, Last => 0);
   begin
      for Step in 0 .. Source.Length + 1 loop
         pragma Loop_Invariant (Valid (P, Source));
         pragma Loop_Invariant (Node_Count (P.Tree) >= Node_Count (P.Tree)'Loop_Entry);
         pragma Loop_Invariant (Pending (P.Tree) >= Mark);
         pragma Loop_Invariant (Limit (P.Budget) = Limit (P.Budget)'Loop_Entry);
         Local_Variable (P, Source, Closing, First_Close, Variable);
         Add_To_List (P, Source, Variable);
         Test_Next (P, Source, Comma, Found);
         exit when not Found;
      end loop;
      Make_List (P, Source, Shape (P, Name_List, Names_First, Names_Line), Mark, Names);
      Test_Next (P, Source, Equals_Sign, Found);
      if Found then
         Expression_List_Of (P, Source, Level, Values);
      end if;
      Item := Shape (P, Local_Statement, First, Line);
      Item.First_Child := Names;
      Item.Second_Child := Values;
      Make (P, Source, Item, Result);
   end Local_Statement;

   --  [puc lparser.c:labelstat] Line is the line of the first '::'.
   procedure Label_Statement
     (P : in out Parser_State;
      Source : Sources.Source;
      Level  : Nesting_Level;
      First  : Source_Position;
      Line   : Line_Number;
      Symbol : Symbol_Index;
      Result : out Node_Index)
   with
     Pre                => Valid (P, Source),
     Post               =>
       Kept (P, Source, Node_Count (P.Tree)'Old, Pending (P.Tree)'Old, Limit (P.Budget)'Old)
       and then Result <= Node_Count (P.Tree),
     Subprogram_Variant => (Decreases => Maximum_Level - Level, Decreases => 1)
   is
      Mark    : constant List_Index := Pending (P.Tree);
      Item    : Node;
      Skipped : Node_Index;
      Label_Last : Span_End;
   begin
      Check_Next (P, Source, Double_Colon);
      Label_Last := P.Previous_Last;
      --  The no-op statements that follow (';' and labels) are read first, as PUC does.
      for Step in 0 .. Source.Length + 1 loop
         exit when P.Failed or else P.Current.Kind not in Semicolon | Double_Colon;
         pragma Loop_Invariant (Valid (P, Source));
         pragma Loop_Invariant (Node_Count (P.Tree) >= Node_Count (P.Tree)'Loop_Entry);
         pragma Loop_Invariant (Pending (P.Tree) >= Mark);
         pragma Loop_Invariant (Limit (P.Budget) = Limit (P.Budget)'Loop_Entry);
         Statement (P, Source, Level, Skipped);
         Add_To_List (P, Source, Skipped);
      end loop;
      Item := Shape (P, Label_Statement, First, Line);
      Item.Last := Label_Last;
      Item.Symbol := Symbol;
      Item.Is_Last_Label := Block_Follow (P, With_Until => False);
      Item.Check_Point := (Ordinal => P.Current.Ordinal, During => Resolving);
      Item.Check_Line := Pyro.Lexer.Line (P.Lexer);
      Make_List (P, Source, Item, Mark, Result);
   end Label_Statement;

   --  [puc lparser.c:retstat] 'return' [explist] [';']
   procedure Return_Statement
     (P : in out Parser_State;
      Source : Sources.Source;
      Level  : Nesting_Level;
      First  : Source_Position;
      Line   : Line_Number;
      Result : out Node_Index)
   with
     Pre                => Valid (P, Source),
     Post               =>
       Kept (P, Source, Node_Count (P.Tree)'Old, Pending (P.Tree)'Old, Limit (P.Budget)'Old)
       and then Result <= Node_Count (P.Tree),
     Subprogram_Variant => (Decreases => Maximum_Level - Level, Decreases => 3)
   is
      Values : Node_Index := No_Node;
      Item   : Node;
   begin
      if not P.Failed
        and then not Block_Follow (P, With_Until => True)
        and then P.Current.Kind /= Semicolon
      then
         Expression_List_Of (P, Source, Level, Values);
      end if;
      if not P.Failed and then P.Current.Kind = Semicolon then
         Next (P, Source);
      end if;
      Item := Shape (P, Return_Statement, First, Line);
      Item.First_Child := Values;
      Make (P, Source, Item, Result);
   end Return_Statement;

   --  [puc lparser.c:restassign] Adds Variable to the assignment's targets, wrapped in an
   --  Assignment_Target that records when PUC checks it is not constant (check_readonly, made
   --  looking at the token after it). Only names and indexed expressions can be assigned
   --  (vkisvar).
   procedure Add_Target (P : in out Parser_State; Source : Sources.Source; Variable : Node_Index)
   with
     Pre  => Valid (P, Source) and then Variable <= Node_Count (P.Tree),
     Post =>
       Valid (P, Source)
       and then Node_Count (P.Tree) >= Node_Count (P.Tree)'Old
       and then Pending (P.Tree) >= Pending (P.Tree)'Old
       and then Limit (P.Budget) = Limit (P.Budget)'Old
   is
      Item    : Node;
      Wrapped : Node_Index;
   begin
      if Variable = No_Node
        or else Get (P.Tree, Variable).Kind not in Name_Expression | Index_Expression
      then
         Syntax_Error (P, Source, (What => Not_Assignable, others => <>));
         return;
      end if;
      Item := Get (P.Tree, Variable);
      Item.Kind := Assignment_Target;
      Item.First_Child := Variable;
      Item.Second_Child := No_Node;
      Item.Third_Child := No_Node;
      Item.Check_Point := (Ordinal => P.Current.Ordinal, During => Resolving);
      Item.Check_Line := Pyro.Lexer.Line (P.Lexer);
      Make (P, Source, Item, Wrapped);
      Add_To_List (P, Source, Wrapped);
   end Add_Target;

   --  [puc lparser.c:restassign] The rest of an assignment whose first target is Target:
   --  more targets, '=', then the values. Each extra target counts a level, as in PUC Lua.
   procedure Assignment_Statement
     (P : in out Parser_State;
      Source : Sources.Source;
      Level  : Nesting_Level;
      First  : Source_Position;
      Line   : Line_Number;
      Target : Node_Index;
      Result : out Node_Index)
   with
     Pre                => Valid (P, Source) and then Target <= Node_Count (P.Tree),
     Post               =>
       Kept (P, Source, Node_Count (P.Tree)'Old, Pending (P.Tree)'Old, Limit (P.Budget)'Old)
       and then Result <= Node_Count (P.Tree),
     Subprogram_Variant => (Decreases => Maximum_Level - Level, Decreases => 8)
   is
      Mark       : constant List_Index := Pending (P.Tree);
      Variable   : Node_Index := Target;
      Targets    : Node_Index;
      Values     : Node_Index := No_Node;
      Item       : Node;
      Found      : Boolean;
      Overflow   : Boolean;
      Current_Level : Nesting_Level := Level;
   begin
      for Step in 0 .. Source.Length + 1 loop
         pragma Loop_Invariant (Valid (P, Source));
         pragma Loop_Invariant (Node_Count (P.Tree) >= Node_Count (P.Tree)'Loop_Entry);
         pragma Loop_Invariant (Pending (P.Tree) >= Mark);
         pragma Loop_Invariant (Variable <= Node_Count (P.Tree));
         pragma Loop_Invariant (Current_Level >= Level);
         pragma Loop_Invariant (Limit (P.Budget) = Limit (P.Budget)'Loop_Entry);
         exit when P.Failed;
         Add_Target (P, Source, Variable);
         exit when P.Failed;
         Test_Next (P, Source, Comma, Found);
         exit when not Found or else P.Failed;
         Suffixed_Expression (P, Source, Current_Level, False, Variable);
         Enter_Level (P, Source, Current_Level, Overflow);
         exit when Overflow;
         Current_Level := Current_Level + 1;
      end loop;
      Make_List (P, Source, Shape (P, Expression_List, First, Line), Mark, Targets);
      Check_Next (P, Source, Equals_Sign);
      if not P.Failed then
         Expression_List_Of (P, Source, Current_Level, Values);
      end if;
      Item := Shape (P, Assignment, First, Line);
      Item.First_Child := Targets;
      Item.Second_Child := Values;
      Make (P, Source, Item, Result);
   end Assignment_Statement;

   --  [puc lparser.c:exprstat] A call, or an assignment.
   procedure Expression_Statement
     (P : in out Parser_State;
      Source : Sources.Source;
      Level  : Nesting_Level;
      Result : out Node_Index)
   with
     Pre                => Valid (P, Source),
     Post               =>
       Kept (P, Source, Node_Count (P.Tree)'Old, Pending (P.Tree)'Old, Limit (P.Budget)'Old)
       and then Result <= Node_Count (P.Tree),
     Subprogram_Variant => (Decreases => Maximum_Level - Level, Decreases => 9)
   is
      First      : constant Source_Position := P.Current.First;
      Line       : constant Line_Number := Pyro.Lexer.Line (P.Lexer);
      Expression : Node_Index;
      Item       : Node;
   begin
      Suffixed_Expression (P, Source, Level, True, Expression);
      Result := No_Node;
      if P.Failed then
         return;
      end if;
      if P.Current.Kind in Equals_Sign | Comma then
         Assignment_Statement (P, Source, Level, First, Line, Expression, Result);
      elsif Expression = No_Node
        or else Get (P.Tree, Expression).Kind not in Call_Expression | Method_Call
      then
         --  [puc lparser.c:exprstat] "syntax error": only calls are statements.
         Syntax_Error
           (P, Source,
            (What      => Not_A_Statement,
             Has_Place => True,
             Place     => (First => First, Last => P.Previous_Last),
             others    => <>));
      else
         Item := Shape (P, Call_Statement, First, Line);
         Item.First_Child := Expression;
         Make (P, Source, Item, Result);
      end if;
   end Expression_Statement;

   procedure Statement
     (P : in out Parser_State;
      Source : Sources.Source;
      Level : Nesting_Level;
      Result : out Node_Index)
   is
      Line     : constant Line_Number := Pyro.Lexer.Line (P.Lexer);
      First    : constant Source_Position := P.Current.First;
      Opener   : constant Span := Current_Span (P);
      Overflow : Boolean;
      Inner    : Node_Index;
      Item     : Node;
      Found    : Boolean;
      Symbol   : Symbol_Index;
   begin
      Result := No_Node;
      Enter_Level (P, Source, Level, Overflow);
      if Overflow or else P.Failed then
         return;
      end if;
      case P.Current.Kind is
         when Semicolon =>
            Next (P, Source);
         when Keyword_If =>
            If_Statement (P, Source, Level + 1, Line, Result);
         when Keyword_While =>
            While_Statement (P, Source, Level + 1, Line, Result);
         when Keyword_Do =>
            Next (P, Source);
            Block_Of (P, Source, Level + 1, Inner);
            Check_Match (P, Source, Keyword_End, Keyword_Do, Line, Opener);
            Item := Shape (P, Do_Statement, First, Line);
            Item.First_Child := Inner;
            Make (P, Source, Item, Result);
         when Keyword_For =>
            For_Statement (P, Source, Level + 1, Line, Result);
         when Keyword_Repeat =>
            Repeat_Statement (P, Source, Level + 1, Line, Result);
         when Keyword_Function =>
            Function_Statement (P, Source, Level + 1, Line, Result);
         when Keyword_Local =>
            Next (P, Source);
            declare
               Function_Opener : constant Span := Current_Span (P);
            begin
               Test_Next (P, Source, Keyword_Function, Found);
               if Found then
                  Local_Function (P, Source, Level + 1, First, Line, Function_Opener, Result);
               else
                  Local_Statement (P, Source, Level + 1, First, Line, Result);
               end if;
            end;
         when Double_Colon =>
            Next (P, Source);
            Check_Name (P, Source, Symbol);
            Label_Statement (P, Source, Level + 1, First, Line, Symbol, Result);
         when Keyword_Return =>
            Next (P, Source);
            Return_Statement (P, Source, Level + 1, First, Line, Result);
         when Keyword_Break =>
            --  [puc lparser.c:breakstat]
            Item := Shape (P, Break_Statement, First, Line);
            Item.Last := P.Current.Last;
            Next (P, Source);
            Make (P, Source, Item, Result);
         when Keyword_Goto =>
            --  [puc lparser.c:gotostat] The goto's line is the line of its label name.
            Next (P, Source);
            Item := Shape (P, Goto_Statement, First, Pyro.Lexer.Line (P.Lexer));
            Check_Name (P, Source, Symbol);
            Item.Symbol := Symbol;
            Item.Last := P.Previous_Last;
            Make (P, Source, Item, Result);
         when others =>
            Expression_Statement (P, Source, Level + 1, Result);
      end case;
   end Statement;

   procedure Parse
     (Source   : Sources.Source;
      Symbols  : in out Symbol_Table;
      Budget   : in out Memory_Budget;
      Tree     : in out Syntax_Tree;
      Problems : in out Diagnostic_Lists.Growable_Array;
      Root     : out Node_Index)
   is
      P : Parser_State;
      Mark       : List_Index;
      Statements : Node_Index;
      Item       : Node;
   begin
      Begin_Parse (P, Source, Symbols, Budget, Tree, Problems);
      Mark := Pending (P.Tree);
      Statement_List (P, Source, 0);
      if not P.Failed and then P.Current.Kind /= End_Of_Stream then
         Error_Expected (P, Source, End_Of_Stream);
      end if;
      Item := Shape (P, Block, 1, 1);
      Item.Is_Incomplete := P.Failed;
      Make_List (P, Source, Item, Mark, Statements);
      Item := Shape (P, Function_Body, 1, 1);
      Item.Second_Child := Statements;
      Item.Is_Vararg := True;
      Item.Is_Incomplete := P.Failed;
      --  [puc lparser.c:close_func] The main function closes at the end of the chunk.
      Item.Check_Point := (Ordinal => P.Current.Ordinal, During => Resolving);
      Item.Check_Line := Pyro.Lexer.Line (P.Lexer);
      Make (P, Source, Item, Root);
      End_Parse (P, Source, Symbols, Budget, Tree, Problems);
      --  [proof] The parser's memory is released.
      pragma Assert
        (Is_Released (P.Symbols)
         and then Is_Released (P.Tree)
         and then Diagnostic_Lists.Is_Released (P.Problems)
         and then Is_Released (P.Lexer)
         and then Character_Arrays.Is_Released (P.Brackets));
   end Parse;

end Pyro.Parser;
