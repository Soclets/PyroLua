--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  The parser's state and its small steps: reading tokens, reporting errors, building nodes,
--  recovering from errors and counting nesting levels.

package body Pyro.Parser.Steps with SPARK_Mode => On is

   --  [proof] The parser's parts are consistent with Source.
   function Valid (P : Parser_State; Source : Sources.Source) return Boolean
   is (Is_Valid (P.Lexer, Source)
       and then Is_Valid (P.Symbols)
       and then Is_Well_Formed (P.Tree)
       and then (if Failed (P.Lexer) then P.Stopped)
       and then (if P.Stopped then P.Failed)
       and then Natural (P.Current.Last) <= Source.Length
       and then Natural (P.Ahead.Last) <= Source.Length
       and then Natural (P.Previous_Last) <= Source.Length
       and then P.Current.Symbol <= Count (P.Symbols)
       and then P.Ahead.Symbol <= Count (P.Symbols));

   procedure Report
     (Problems : in out Diagnostic_Lists.Growable_Array;
      Budget   : in out Memory_Budget;
      Item     : Diagnostic;
      Failed   : in out Boolean;
      Stopped  : in out Boolean)
   is
      Success : Boolean;
   begin
      Diagnostic_Lists.Append (Problems, Item, Budget, Success);
      if not Success then
         Failed := True;
         Stopped := True;
      end if;
   end Report;

   procedure Stop_For_Memory (P : in out Parser_State; Source : Sources.Source)
   is
      pragma Unreferenced (Source);
   begin
      if not P.Stopped then
         P.Stopped := True;
         P.Failed := True;
         Report (P.Problems, P.Budget, (What => Not_Enough_Memory, others => <>), P.Failed,
                 P.Stopped);
      end if;
   end Stop_For_Memory;

   procedure Describe_Current
     (P : in out Parser_State; Source : Sources.Source; Item : in out Diagnostic; Near : Boolean)
   is
      pragma Unreferenced (Source);
   begin
      Item.Has_Place := True;
      Item.Place := Current_Span (P);
      Item.Found := P.Current.Kind;
      Item.Found_Byte := P.Current.Byte;
      Item.Has_Lua_Line := True;
      Item.Lua_Line := Line (P.Lexer);
      Item.Detection := (Ordinal => P.Current.Ordinal, During => Parsing);
      if Near then
         if P.Current.Kind in Token_With_Text then
            --  [puc llex.c:txtToken] The text of the token read last.
            Item.Near := Near_Text;
            Token_Text (P.Lexer, P.Symbols, P.Budget, Item.Near_Text);
         else
            Item.Near := Near_Token;
            Item.Near_Token := P.Current.Kind;
            Item.Near_Byte := P.Current.Byte;
         end if;
      end if;
   end Describe_Current;

   procedure Report_Current
     (P : in out Parser_State; Source : Sources.Source; Template : Diagnostic; Near : Boolean)
   is
      Item : Diagnostic := Template;
      Place : constant Span := Template.Place;
   begin
      Describe_Current (P, Source, Item, Near);
      if Template.Has_Place then
         Item.Place := Place;
      end if;
      Report (P.Problems, P.Budget, Item, P.Failed, P.Stopped);
   end Report_Current;

   procedure Syntax_Error (P : in out Parser_State; Source : Sources.Source; Template : Diagnostic)
   is
   begin
      if not P.Failed then
         Report_Current (P, Source, Template, Near => True);
      end if;
      P.Failed := True;
   end Syntax_Error;

   procedure Error_Expected
     (P : in out Parser_State;
      Source : Sources.Source;
      Expected : Spelled_Token)
   is
   begin
      Syntax_Error (P, Source, (What => Token_Expected, Expected => Expected, others => <>));
   end Error_Expected;

   procedure Next (P : in out Parser_State; Source : Sources.Source)
   is
   begin
      P.Previous_Last := P.Current.Last;
      if P.Has_Ahead then
         P.Current := P.Ahead;
         P.Has_Ahead := False;
      elsif P.Stopped then
         P.Current.Kind := End_Of_Stream;
      else
         Next_Token (P.Lexer, Source, P.Symbols, P.Budget, P.Current);
         if Failed (P.Lexer) then
            P.Stopped := True;
            P.Failed := True;
            Report (P.Problems, P.Budget, Error (P.Lexer), P.Failed, P.Stopped);
         end if;
      end if;
   end Next;

   procedure Look_Ahead (P : in out Parser_State; Source : Sources.Source)
   is
   begin
      if P.Stopped then
         P.Ahead := P.Current;
         P.Ahead.Kind := End_Of_Stream;
         P.Has_Ahead := True;
         return;
      end if;
      Next_Token (P.Lexer, Source, P.Symbols, P.Budget, P.Ahead);
      P.Has_Ahead := True;
      if Failed (P.Lexer) then
         P.Stopped := True;
         P.Failed := True;
         Report (P.Problems, P.Budget, Error (P.Lexer), P.Failed, P.Stopped);
      end if;
   end Look_Ahead;

   procedure Test_Next
     (P : in out Parser_State; Source : Sources.Source; Kind : Token_Kind; Found : out Boolean)
   is
   begin
      Found := not P.Failed and then P.Current.Kind = Kind;
      if Found then
         Next (P, Source);
      end if;
   end Test_Next;

   procedure Check_Next (P : in out Parser_State; Source : Sources.Source; Kind : Spelled_Token)
   is
   begin
      if P.Failed then
         return;
      elsif P.Current.Kind /= Kind then
         Error_Expected (P, Source, Kind);
      else
         Next (P, Source);
      end if;
   end Check_Next;

   procedure Check_Match
     (P : in out Parser_State;
      Source : Sources.Source;
      What   : Spelled_Token;
      Who    : Spelled_Token;
      Where  : Line_Number;
      Opener : Span)
   is
      Found : Boolean;
   begin
      if P.Failed then
         return;
      end if;
      Test_Next (P, Source, What, Found);
      if not Found and then not P.Failed then
         Syntax_Error
           (P, Source,
            (What       => (if Where = Line (P.Lexer) then Token_Expected
                            else Token_Expected_To_Close),
             Expected   => What,
             Opener     => Who,
             Other_Line => Where,
             Links      => 1,
             First_Link => Opener,
             others     => <>));
      end if;
   end Check_Match;

   procedure Expect_Closer
     (P      : in out Parser_State;
      Source : Sources.Source;
      What   : Spelled_Token;
      Who    : Spelled_Token;
      Where  : Line_Number;
      Opener : Span) is
   begin
      if not P.Failed and then P.Current.Kind /= What then
         Syntax_Error
           (P, Source,
            (What       => (if Where = Line (P.Lexer) then Token_Expected
                            else Token_Expected_To_Close),
             Expected   => What,
             Opener     => Who,
             Other_Line => Where,
             Links      => 1,
             First_Link => Opener,
             others     => <>));
      end if;
   end Expect_Closer;

   procedure Check_Name
     (P : in out Parser_State;
      Source : Sources.Source;
      Symbol : out Symbol_Index)
   is
   begin
      Symbol := No_Symbol;
      if P.Failed then
         return;
      elsif P.Current.Kind /= Name then
         Error_Expected (P, Source, Name);
      else
         Symbol := P.Current.Symbol;
         Next (P, Source);
      end if;
   end Check_Name;

   procedure Make
     (P : in out Parser_State;
      Source : Sources.Source;
      Item : Node;
      Result : out Node_Index)
   is
   begin
      Add_Node (P.Tree, P.Budget, Item, Result);
      if Result = No_Node then
         Stop_For_Memory (P, Source);
      end if;
   end Make;

   procedure Make_List
     (P : in out Parser_State; Source : Sources.Source; Item : Node; Mark : List_Index;
      Result : out Node_Index)
   is
   begin
      Add_List_Node (P.Tree, P.Budget, Item, Mark, Result);
      if Result = No_Node then
         Stop_For_Memory (P, Source);
      end if;
   end Make_List;

   procedure Add_To_List (P : in out Parser_State; Source : Sources.Source; Item : Node_Index)
   is
      Success : Boolean;
   begin
      if Item /= No_Node then
         Push (P.Tree, P.Budget, Item, Success);
         if not Success then
            Stop_For_Memory (P, Source);
         end if;
      end if;
   end Add_To_List;

   procedure Recover (P : in out Parser_State; Source : Sources.Source; Opener : Token_Kind)
   is
      Success : Boolean;
      Length  : Character_Arrays.Extended_Index;
      Intact  : Boolean := False;
   begin
      if not P.Failed or else P.Stopped then
         return;
      end if;
      Character_Arrays.Truncate (P.Brackets, 0);
      --  Every step reads a token, and every token but the last uses at least one byte.
      for Step in 0 .. Source.Length + 1 loop
         pragma Loop_Invariant (Valid (P, Source));
         pragma Loop_Invariant (P.Failed and then not Intact);
         pragma Loop_Invariant (Node_Count (P.Tree) = Node_Count (P.Tree)'Loop_Entry);
         pragma Loop_Invariant (Pending (P.Tree) = Pending (P.Tree)'Loop_Entry);
         pragma Loop_Invariant (Limit (P.Budget) = Limit (P.Budget)'Loop_Entry);
         exit when P.Stopped or else P.Current.Kind = End_Of_Stream;
         Length := Character_Arrays.Length (P.Brackets);
         if Is_Opening (P.Current.Kind) then
            Character_Arrays.Append (P.Brackets, Byte_Of (P.Current.Kind), P.Budget, Success);
            if not Success then
               Stop_For_Memory (P, Source);
               exit;
            end if;
         elsif Is_Closing (P.Current.Kind) then
            if Length = 0 then
               Intact := P.Current.Kind = Closer_Of (Opener);
               exit;
            elsif Closer_Of (Kind_Of_Byte (Character_Arrays.Element (P.Brackets, Length)))
                  /= P.Current.Kind
            then
               exit;
            end if;
            Character_Arrays.Truncate (P.Brackets, Length - 1);
         end if;
         Next (P, Source);
      end loop;
      if Intact then
         P.Failed := False;
      else
         P.Stopped := True;
      end if;
   end Recover;

   procedure Enter_Level
     (P : in out Parser_State;
      Source : Sources.Source;
      Level : Nesting_Level;
      Overflow : out Boolean)
   is
      Item : Diagnostic := (What => Nesting_Too_Deep, others => <>);
   begin
      Overflow := Natural (Level) + 1 + Calls_Before_Parsing >= Maximum_C_Calls;
      if Overflow then
         if not P.Failed then
            Describe_Current (P, Source, Item, Near => False);
            Item.Has_Lua_Line := False;
            P.Failed := True;
            P.Stopped := True;
            Report (P.Problems, P.Budget, Item, P.Failed, P.Stopped);
         else
            P.Stopped := True;
         end if;
      end if;
   end Enter_Level;

   procedure Set_Vararg (P : in out Parser_State; Source : Sources.Source; Value : Boolean) is
      pragma Unreferenced (Source);
   begin
      P.In_Vararg := Value;
   end Set_Vararg;

   function Is_Attribute
     (P      : Parser_State;
      Source : Sources.Source;
      Symbol : Symbol_Index;
      Name   : String) return Boolean
   is (Symbol /= No_Symbol
       and then Length (P.Symbols, Symbol) = Name'Length
       and then Text (P.Symbols, Symbol) = Name);

   procedure Begin_Parse
     (P : in out Parser_State;
      Source   : Sources.Source;
      Symbols  : in out Symbol_Table;
      Budget   : Memory_Budget;
      Tree     : in out Syntax_Tree;
      Problems : in out Diagnostic_Lists.Growable_Array) is
   begin
      Swap (P.Symbols, Symbols);
      Swap (P.Tree, Tree);
      Diagnostic_Lists.Swap (P.Problems, Problems);
      P.Budget := Budget;
      Start (P.Lexer, Source, P.Budget);
      P.Current := (others => <>);
      P.Ahead := (others => <>);
      P.Has_Ahead := False;
      P.Previous_Last := 0;
      P.Failed := False;
      P.Stopped := False;
      --  [puc lparser.c:mainfunc] The main function is vararg.
      P.In_Vararg := True;
      Next (P, Source);
   end Begin_Parse;

   procedure End_Parse
     (P : in out Parser_State;
      Source   : Sources.Source;
      Symbols  : in out Symbol_Table;
      Budget   : out Memory_Budget;
      Tree     : in out Syntax_Tree;
      Problems : in out Diagnostic_Lists.Growable_Array)
   is
      pragma Unreferenced (Source);
   begin
      Drop_Pending (P.Tree, 0);
      Clear (P.Lexer, P.Budget);
      Character_Arrays.Clear (P.Brackets, P.Budget);
      Swap (P.Symbols, Symbols);
      Swap (P.Tree, Tree);
      Diagnostic_Lists.Swap (P.Problems, Problems);
      Budget := P.Budget;
   end End_Parse;

end Pyro.Parser.Steps;
