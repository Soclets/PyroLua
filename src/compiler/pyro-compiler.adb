--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  The compiler: turns a chunk's syntax tree into the prototypes PUC Lua's luac would produce.
--
--  The walk visits the tree in the order PUC Lua's lparser.c reads the source and makes the
--  calls lparser.c makes into lcode.c (Pyro.Compiler.Code) at the same points. luac gives each
--  instruction the line of the token read last; the walk keeps that token up to date (Consume)
--  from the tokens of the chunk, which it reads again first.

with Pyro.Character_Arrays;
with Pyro.Compiler.Code;   use Pyro.Compiler.Code;
with Pyro.Compiler.Code.Scopes; use Pyro.Compiler.Code.Scopes;
with Pyro.Diagnostics;     use Pyro.Diagnostics;
with Pyro.Integer_Arithmetic;
with Pyro.Lexer;
with Pyro.Tokens;          use Pyro.Tokens;

package body Pyro.Compiler with SPARK_Mode => On is

   --  What every step of the walk needs.
   function Ready
     (Result : Chunk; Tree : Syntax_Tree; Symbols : Symbol_Table; Node : Node_Index)
      return Boolean
   is (Is_Well_Formed (Tree)
       and then Node in 1 .. Node_Count (Tree)
       and then Is_Well_Formed (Result)
       and then Is_Valid (Symbols))
   with Ghost;

   ---------------------------------------------------------------------------------------------
   --  Tokens

   --  The ordinal of the first token of Node.
   function First_Token (State : Compiler_State; Tree : Syntax_Tree; Node : Node_Index)
      return Natural
   is (Token_At (State, Get (Tree, Node).First))
   with Pre => Node in 1 .. Node_Count (Tree);

   --  The ordinal of the last token of Node (0 for a node ending before the first token).
   function Last_Token (State : Compiler_State; Tree : Syntax_Tree; Node : Node_Index)
      return Natural
   is (if Get (Tree, Node).Last = 0 then 0 else Token_At (State, Get (Tree, Node).Last))
   with Pre => Node in 1 .. Node_Count (Tree);

   --  The token after Ordinal, and the one before (no token is ordinal 0).
   function After (Ordinal : Natural) return Natural
   is (if Ordinal < Bounded_Count'Last then Ordinal + 1 else Ordinal);

   function Before (Ordinal : Natural) return Natural
   is (if Ordinal > 0 then Ordinal - 1 else 0);

   --  [puc lparser.c:codestring] A string expression.
   function String_Expression (Symbols : Symbol_Table; Symbol : Symbol_Index) return Expression
   is ((Kind          => String_Value,
        String_Symbol => Symbol,
        String_Short  =>
          Symbol not in 1 .. Count (Symbols)
          or else Natural (Length (Symbols, Symbol)) <= Maximum_Short_String,
        others        => <>))
   with Pre => Is_Valid (Symbols);

   --  The kind of child Slot of Node, Missing for none.
   function Kind_Of (Tree : Syntax_Tree; Node : Node_Index) return Node_Kind
   is (if Node in 1 .. Node_Count (Tree) then Get (Tree, Node).Kind else Missing);

   --  Sets the free register of the open function.
   procedure Set_Free_Register (State : in out Compiler_State; Register : Natural) is
      Item : Function_Entry := Current (State);
   begin
      if Register > 255 then
         Fail (State);
         return;
      end if;
      Item.Free_Register := Register;
      Set_Current (State, Item);
   end Set_Free_Register;

   --  [puc lparser.c:adjust_assign].
   procedure Adjust_Assign
     (State : in out Compiler_State; Variables, Expressions : Natural; Item : in out Expression)
   is
      Needed : constant Integer := Variables - Expressions;
   begin
      if Variables > 1000 or else Expressions > 2 ** 24 then
         Fail (State);
         return;
      end if;
      if Has_Multiple_Results (Item) then
         Set_Returns (State, Item, Integer'Max (Needed + 1, 0));
      else
         if Item.Kind /= Void then
            To_Next_Register (State, Item);
         end if;
         if Needed > 0 then
            Load_Nil (State, Current (State).Free_Register, Needed);
         end if;
      end if;
      if Needed > 0 then
         Reserve_Registers (State, Needed);
      elsif Current (State).Free_Register >= -Needed then
         Set_Free_Register (State, Current (State).Free_Register + Needed);
      else
         Fail (State);
      end if;
   end Adjust_Assign;

   --  [puc lparser.c:fixforjump].
   procedure Fix_For_Jump
     (State : in out Compiler_State; Position, Target : Natural; Back : Boolean)
   is
      Item   : Instruction := Get (State, Position);
      Offset : Integer;
   begin
      if Position >= Entry_Number'Last or else Position >= PC (State)
        or else Target > Entry_Number'Last
      then
         Fail (State);
         return;
      end if;
      Offset := Target - (Position + 1);
      if Back then
         Offset := -Offset;
      end if;
      if Offset > Maximum_Bx then
         Raise_Error (State, Control_Structure_Too_Long, 0);
         return;
      elsif Offset < 0 then
         Fail (State);
         return;
      end if;
      Item.Wide := Wide_Argument (Offset);
      Put (State, Position, Item);
   end Fix_For_Jump;

   ---------------------------------------------------------------------------------------------
   --  Expressions

   procedure Expression_Of
     (State : in out Compiler_State; Result : in out Chunk; Tree : Syntax_Tree;
      Symbols : Symbol_Table; Node : Node_Index; Item : out Expression)
   with
     Pre                => Ready (Result, Tree, Symbols, Node),
     Post               => Is_Well_Formed (Result),
     Subprogram_Variant => (Decreases => Node, Decreases => 14);

   procedure Expression_List_Of
     (State : in out Compiler_State; Result : in out Chunk; Tree : Syntax_Tree;
      Symbols : Symbol_Table; Node : Node_Index; Item : out Expression; Count : out Natural)
   with
     Pre                => Ready (Result, Tree, Symbols, Node),
     Post               => Is_Well_Formed (Result),
     Subprogram_Variant => (Decreases => Node, Decreases => 10);

   procedure Function_Body_Of
     (State : in out Compiler_State; Result : in out Chunk; Tree : Syntax_Tree;
      Symbols : Symbol_Table; Node : Node_Index; Is_Method : Boolean; Item : out Expression)
   with
     Pre                => Ready (Result, Tree, Symbols, Node),
     Post               => Is_Well_Formed (Result),
     Subprogram_Variant => (Decreases => Node, Decreases => 15);

   procedure Statement_List
     (State : in out Compiler_State; Result : in out Chunk; Tree : Syntax_Tree;
      Symbols : Symbol_Table; Node : Node_Index; From : List_Index)
   with
     Pre                => Ready (Result, Tree, Symbols, Node),
     Post               => Is_Well_Formed (Result),
     Subprogram_Variant => (Decreases => Node, Decreases => 16);

   --  [puc lparser.c:explist] Item is the last expression, still open; the others are in
   --  consecutive registers.
   procedure Expression_List_Of
     (State : in out Compiler_State; Result : in out Chunk; Tree : Syntax_Tree;
      Symbols : Symbol_Table; Node : Node_Index; Item : out Expression; Count : out Natural)
   is
      Length   : constant List_Index := Get (Tree, Node).List_Length;
      Previous : Node_Index := No_Node;
      Element  : Node_Index;
   begin
      Item := Make (Void);
      Count := 0;
      for Position in 1 .. Length loop
         pragma Loop_Invariant (Is_Well_Formed (Result));
         pragma Loop_Invariant (Count <= Natural (Position) - 1);
         pragma Loop_Invariant (Previous < Node);
         Element := List_Item (Tree, Node, Position);
         if Previous /= No_Node then
            Consume (State, After (Last_Token (State, Tree, Previous)));
            declare
               Unused_Copy : Expression := Item;
            begin
               To_Next_Register (State, Unused_Copy);
            end;
         end if;
         Expression_Of (State, Result, Tree, Symbols, Element, Item);
         Count := Count + 1;
         Previous := Element;
         exit when Failed (State);
      end loop;
   end Expression_List_Of;

   --  [puc lparser.c:constructor].
   procedure Constructor_Of
     (State : in out Compiler_State; Result : in out Chunk; Tree : Syntax_Tree;
      Symbols : Symbol_Table; Node : Node_Index; Item : out Expression)
   with
     Pre                => Ready (Result, Tree, Symbols, Node),
     Post               => Is_Well_Formed (Result),
     Subprogram_Variant => (Decreases => Node, Decreases => 11)
   is
      Open       : constant Natural := First_Token (State, Tree, Node);
      Table_At   : Natural;
      Array_Size : Integer := 0;
      Hash_Size  : Natural := 0;
      To_Store   : Natural := 0;
      Pending    : Expression := Make (Void);
      Field      : Node_Index;
      Previous   : Node_Index := No_Node;
      Key        : Expression;
      Value      : Expression;
      Table      : Expression;
      Free       : Natural;
      Key_Node   : Node_Index;
      Value_Node : Node_Index;
   begin
      --  NEWTABLE is coded before '{' is read.
      Consume (State, Before (Open));
      Code_ABC (State, New_Table, 0, 0, 0, False, Table_At);
      Code_Raw (State, (others => <>));
      Item := Make (Fixed_Register, Current (State).Free_Register);
      Reserve_Registers (State, 1);
      Consume (State, Open);
      for Position in 1 .. Get (Tree, Node).List_Length loop
         pragma Loop_Invariant (Is_Well_Formed (Result));
         pragma Loop_Invariant (Previous < Node);
         exit when Failed (State);
         Field := List_Item (Tree, Node, Position);
         if Previous /= No_Node then
            --  The separator.
            Consume (State, After (Last_Token (State, Tree, Previous)));
         end if;
         --  [puc lparser.c:closelistfield]
         if Pending.Kind /= Void then
            declare
               Unused_Copy : Expression := Pending;
            begin
               To_Next_Register (State, Unused_Copy);
            end;
            Pending := Make (Void);
            if To_Store = Fields_Per_Flush then
               Set_List (State, Item.Info, Natural'Max (Array_Size, 0), To_Store);
               Array_Size := Integer'Min (Array_Size, 2 ** 29) + To_Store;
               To_Store := 0;
            end if;
         end if;
         if Kind_Of (Tree, Field) = Named_Field then
            --  [puc lparser.c:recfield]
            Free := Current (State).Free_Register;
            Key_Node := Child (Tree, Field, 1);
            Value_Node := Child (Tree, Field, 2);
            if Key_Node = No_Node or else Value_Node = No_Node then
               Fail (State);
               return;
            end if;
            if Get (Tree, Field).Is_Name_Key then
               --  PUC Lua looked past the name for '=' before reading it.
               Consume (State, After (First_Token (State, Tree, Key_Node)));
               Key := String_Expression (Symbols, Get (Tree, Key_Node).Symbol);
            else
               Consume (State, Before (First_Token (State, Tree, Key_Node)));
               Expression_Of (State, Result, Tree, Symbols, Key_Node, Key);
               To_Value (State, Key);
               Consume (State, After (After (Last_Token (State, Tree, Key_Node))));
            end if;
            Hash_Size := Natural'Min (Hash_Size, 2 ** 29) + 1;
            Table := Item;
            Indexed (State, Table, Key);
            Expression_Of (State, Result, Tree, Symbols, Value_Node, Value);
            declare
               Unused_Copy : Expression := Value;
            begin
               Store_Variable (State, Table, Unused_Copy);
            end;
            Set_Free_Register (State, Free);
         else
            --  [puc lparser.c:listfield]: a name first is read after looking past it.
            if Token_Kind_At (State, First_Token (State, Tree, Field)) = Name then
               Set_Lookahead_Name (State, First_Token (State, Tree, Field));
            end if;
            Expression_Of (State, Result, Tree, Symbols, Field, Pending);
            Set_Lookahead_Name (State, 0);
            To_Store := Natural'Min (To_Store, 2 ** 29) + 1;
         end if;
         Previous := Field;
      end loop;
      Consume (State, Last_Token (State, Tree, Node));
      --  [puc lparser.c:lastlistfield]
      if To_Store /= 0 then
         if Has_Multiple_Results (Pending) then
            Set_Returns (State, Pending, Multiple_Results);
            Set_List (State, Item.Info, Natural'Max (Array_Size, 0), Multiple_Results);
            Array_Size := Integer'Max (Integer'Min (Array_Size, 2 ** 29), -1) - 1;
         else
            if Pending.Kind /= Void then
               declare
                  Unused_Copy : Expression := Pending;
               begin
                  To_Next_Register (State, Unused_Copy);
               end;
            end if;
            Set_List (State, Item.Info, Natural'Max (Array_Size, 0), To_Store);
         end if;
         Array_Size := Integer'Max (Integer'Min (Array_Size, 2 ** 29), -2)
                       + Natural'Min (To_Store, 2 ** 29);
      end if;
      Set_Table_Size (State, Table_At, Item.Info, Natural'Max (Array_Size, 0), Hash_Size);
   end Constructor_Of;

   --  [puc lparser.c:funcargs] Arguments of call Node to the function in Callee.
   procedure Arguments_Of
     (State : in out Compiler_State; Result : in out Chunk; Tree : Syntax_Tree;
      Symbols : Symbol_Table; Node : Node_Index; Open : Natural; Callee : in out Expression)
   with
     Pre                => Ready (Result, Tree, Symbols, Node),
     Post               => Is_Well_Formed (Result),
     Subprogram_Variant => (Decreases => Node, Decreases => 11)
   is
      Line      : constant Line_Number := Token_Line (State, Open);
      Arguments : Expression := Make (Void);
      Ignored_Count : Natural;
      Base      : constant Natural := Natural'Min (Callee.Info, 255);
      Parameters : Integer;
      Position  : Natural;
      First     : Node_Index;
   begin
      case Token_Kind_At (State, Open) is
         when Left_Parenthesis =>
            Consume (State, Open);
            if Get (Tree, Node).List_Length > 0 then
               Expression_List_Of
                 (State, Result, Tree, Symbols, Node, Arguments, Ignored_Count);
               if Has_Multiple_Results (Arguments) then
                  Set_Returns (State, Arguments, Multiple_Results);
               end if;
            end if;
            Consume (State, Last_Token (State, Tree, Node));
         when Left_Brace =>
            if Get (Tree, Node).List_Length /= 1 then
               Fail (State);
               return;
            end if;
            First := List_Item (Tree, Node, 1);
            Constructor_Of (State, Result, Tree, Symbols, First, Arguments);
         when String_Literal =>
            if Get (Tree, Node).List_Length /= 1 then
               Fail (State);
               return;
            end if;
            First := List_Item (Tree, Node, 1);
            Arguments := String_Expression (Symbols, Get (Tree, First).Symbol);
            Consume (State, Open);
         when others =>
            Fail (State);
            return;
      end case;
      if Callee.Kind /= Fixed_Register or else Callee.Info > 254 then
         Fail (State);
         return;
      end if;
      if Has_Multiple_Results (Arguments) then
         Parameters := Multiple_Results;
      else
         if Arguments.Kind /= Void then
            declare
               Unused_Argument : Expression := Arguments;
            begin
               To_Next_Register (State, Unused_Argument);
            end;
         end if;
         Parameters := Current (State).Free_Register - (Base + 1);
      end if;
      if Parameters + 1 not in 0 .. 255 then
         Fail (State);
         return;
      end if;
      Code_ABC (State, Call, Base, Parameters + 1, 2, False, Position);
      Callee := Make (Open_Call, Position);
      Fix_Line (State, Line);
      Set_Free_Register (State, Base + 1);
   end Arguments_Of;

   --  [puc lparser.c:suffixedexp] with primaryexp: a name or parenthesized expression followed
   --  by fields, indexes, method calls and calls. The chain is walked with a stack, since it
   --  can be as long as the chunk.
   procedure Suffixed_Expression_Of
     (State : in out Compiler_State; Result : in out Chunk; Tree : Syntax_Tree;
      Symbols : Symbol_Table; Node : Node_Index; Item : out Expression)
   with
     Pre                => Ready (Result, Tree, Symbols, Node),
     Post               => Is_Well_Formed (Result),
     Subprogram_Variant => (Decreases => Node, Decreases => 12)
   is
      Base    : constant Natural := Spine_Length (State);
      Primary : Node_Index := Node;
      Link    : Node_Index;
      Inner   : Node_Index;
      Key     : Expression;
      Success : Boolean := True;
      Name_At : Natural;
   begin
      Item := Make (Void);
      while Kind_Of (Tree, Primary) in Index_Expression | Call_Expression | Method_Call loop
         pragma Loop_Invariant (Primary in 1 .. Node);
         pragma Loop_Variant (Decreases => Primary);
         Push_Node (State, Primary, Success);
         exit when not Success;
         Inner := Child (Tree, Primary, 1);
         exit when Inner = No_Node;
         Primary := Inner;
      end loop;
      if not Success then
         Raise_Error (State, Not_Enough_Memory, 0);
         return;
      end if;
      case Kind_Of (Tree, Primary) is
         when Name_Expression =>
            Consume (State, First_Token (State, Tree, Primary));
            Single_Variable
              (State, Get (Tree, Primary).Symbol,
               String_Expression (Symbols, Get (Tree, Primary).Symbol).String_Short, Item);
         when Parenthesized =>
            Inner := Child (Tree, Primary, 1);
            if Inner = No_Node then
               Fail (State);
               return;
            end if;
            Consume (State, First_Token (State, Tree, Primary));
            Expression_Of (State, Result, Tree, Symbols, Inner, Item);
            Consume (State, Last_Token (State, Tree, Primary));
            Discharge_Variables (State, Item);
         when others =>
            Fail (State);
            return;
      end case;
      for Position in reverse Base + 1 .. Spine_Length (State) loop
         pragma Loop_Invariant (Is_Well_Formed (Result));
         exit when Failed (State);
         Link := Spine_Node (State, Position);
         if Link not in 1 .. Node then
            Fail (State);
            exit;
         end if;
         Inner := Child (Tree, Link, 1);
         case Get (Tree, Link).Kind is
            when Index_Expression =>
               To_Any_Register_Or_Upvalue (State, Item);
               declare
                  Key_Node : constant Node_Index := Child (Tree, Link, 2);
               begin
                  if Key_Node = No_Node or else Inner = No_Node then
                     Fail (State);
                     exit;
                  end if;
                  if Get (Tree, Link).Is_Name_Key then
                     Consume (State, After (After (Last_Token (State, Tree, Inner))));
                     Key := String_Expression (Symbols, Get (Tree, Key_Node).Symbol);
                  else
                     Consume (State, After (Last_Token (State, Tree, Inner)));
                     Expression_Of (State, Result, Tree, Symbols, Key_Node, Key);
                     To_Value (State, Key);
                     Consume (State, Last_Token (State, Tree, Link));
                  end if;
                  Indexed (State, Item, Key);
               end;
            when Method_Call =>
               if Inner = No_Node then
                  Fail (State);
                  exit;
               end if;
               Name_At := After (After (Last_Token (State, Tree, Inner)));
               Consume (State, Name_At);
               Key := String_Expression (Symbols, Get (Tree, Link).Symbol);
               declare
                  Unused_Copy : Expression := Key;
               begin
                  Self_Call (State, Item, Unused_Copy);
               end;
               Arguments_Of (State, Result, Tree, Symbols, Link, After (Name_At), Item);
            when Call_Expression =>
               if Inner = No_Node then
                  Fail (State);
                  exit;
               end if;
               To_Next_Register (State, Item);
               Arguments_Of
                 (State, Result, Tree, Symbols, Link, After (Last_Token (State, Tree, Inner)),
                  Item);
            when others =>
               Fail (State);
               exit;
         end case;
      end loop;
      Truncate_Spine (State, Base);
   end Suffixed_Expression_Of;

   --  [puc lparser.c:simpleexp].
   procedure Simple_Expression_Of
     (State : in out Compiler_State; Result : in out Chunk; Tree : Syntax_Tree;
      Symbols : Symbol_Table; Node : Node_Index; Item : out Expression)
   with
     Pre                => Ready (Result, Tree, Symbols, Node),
     Post               => Is_Well_Formed (Result),
     Subprogram_Variant => (Decreases => Node, Decreases => 13)
   is
      Value    : constant Syntax_Trees.Node := Get (Tree, Node);
      Token    : constant Natural := First_Token (State, Tree, Node);
      Position : Natural;
      Inner    : Node_Index;
   begin
      Item := Make (Void);
      case Value.Kind is
         when Nil_Literal =>
            Item := Make (Nil_Value);
            Consume (State, Token);
         when True_Literal =>
            Item := Make (True_Value);
            Consume (State, Token);
         when False_Literal =>
            Item := Make (False_Value);
            Consume (State, Token);
         when Integer_Literal =>
            Item := (Kind => Integer_Value,
                     Integer_Bits => Integer_Arithmetic.To_Signed (Value.Value), others => <>);
            Consume (State, Token);
         when Float_Literal =>
            Item := (Kind => Float_Value, Float_Bits => Value.Value, others => <>);
            Consume (State, Token);
         when String_Literal =>
            Item := String_Expression (Symbols, Value.Symbol);
            Consume (State, Token);
         when Vararg_Expression =>
            --  VARARG is coded before '...' is read.
            Consume (State, Before (Token));
            Code_ABC (State, Vararg, 0, 0, 1, False, Position);
            Item := Make (Open_Vararg, Position);
            Consume (State, Token);
         when Table_Constructor =>
            Constructor_Of (State, Result, Tree, Symbols, Node, Item);
         when Function_Expression =>
            Inner := Child (Tree, Node, 1);
            if Inner = No_Node then
               Fail (State);
               return;
            end if;
            Consume (State, Token);
            Function_Body_Of (State, Result, Tree, Symbols, Inner, False, Item);
         when Name_Expression | Index_Expression | Call_Expression | Method_Call
            | Parenthesized =>
            Suffixed_Expression_Of (State, Result, Tree, Symbols, Node, Item);
         when others =>
            Fail (State);
      end case;
   end Simple_Expression_Of;

   --  [puc lparser.c:subexpr] Operators that chain to the left (a + b + c) are walked with a
   --  stack, since such a chain can be as long as the chunk.
   procedure Expression_Of
     (State : in out Compiler_State; Result : in out Chunk; Tree : Syntax_Tree;
      Symbols : Symbol_Table; Node : Node_Index; Item : out Expression)
   is
      Base     : constant Natural := Spine_Length (State);
      Operand  : Node_Index := Node;
      Link     : Node_Index;
      Left     : Node_Index;
      Right    : Node_Index;
      Right_Item : Expression;
      Operator : Natural;
      Success  : Boolean := True;
   begin
      Item := Make (Void);
      while Kind_Of (Tree, Operand) = Binary_Operation loop
         pragma Loop_Invariant (Operand in 1 .. Node);
         pragma Loop_Variant (Decreases => Operand);
         Push_Node (State, Operand, Success);
         exit when not Success;
         Left := Child (Tree, Operand, 1);
         exit when Left = No_Node;
         Operand := Left;
      end loop;
      if not Success then
         Raise_Error (State, Not_Enough_Memory, 0);
         return;
      end if;
      if Kind_Of (Tree, Operand) = Unary_Operation then
         Operator := First_Token (State, Tree, Operand);
         Right := Child (Tree, Operand, 1);
         if Right = No_Node then
            Fail (State);
            return;
         end if;
         Consume (State, Operator);
         Expression_Of (State, Result, Tree, Symbols, Right, Item);
         Prefix (State, Get (Tree, Operand).Operator, Item, Token_Line (State, Operator));
      elsif Operand < Node then
         Expression_Of (State, Result, Tree, Symbols, Operand, Item);
      elsif Operand = Node and then Kind_Of (Tree, Operand) /= Binary_Operation then
         Simple_Expression_Of (State, Result, Tree, Symbols, Node, Item);
      else
         Fail (State);
      end if;
      for Position in reverse Base + 1 .. Spine_Length (State) loop
         pragma Loop_Invariant (Is_Well_Formed (Result));
         exit when Failed (State);
         Link := Spine_Node (State, Position);
         if Link not in 1 .. Node then
            Fail (State);
            exit;
         end if;
         Left := Child (Tree, Link, 1);
         Right := Child (Tree, Link, 2);
         if Left = No_Node or else Right = No_Node then
            Fail (State);
            exit;
         end if;
         Operator := After (Last_Token (State, Tree, Left));
         Consume (State, Operator);
         Infix (State, Get (Tree, Link).Operator, Item);
         Expression_Of (State, Result, Tree, Symbols, Right, Right_Item);
         declare
            Unused_Copy : Expression := Right_Item;
         begin
            Posfix (State, Get (Tree, Link).Operator, Item, Unused_Copy,
                    Token_Line (State, Operator));
         end;
      end loop;
      Truncate_Spine (State, Base);
   end Expression_Of;

   --  [puc lparser.c:body] The function of Function_Body Node, as a closure in the next
   --  register of the enclosing function.
   procedure Function_Body_Of
     (State : in out Compiler_State; Result : in out Chunk; Tree : Syntax_Tree;
      Symbols : Symbol_Table; Node : Node_Index; Is_Method : Boolean; Item : out Expression)
   is
      Value       : constant Syntax_Trees.Node := Get (Tree, Node);
      Parameters  : constant Node_Index := Child (Tree, Node, 1);
      Body_Block  : constant Node_Index := Child (Tree, Node, 2);
      Ignored_Index : Natural;
      Count       : Natural := 0;
      Facts       : Function_Entry;
      Close_Paren : Natural;
      Position    : Natural;
      Parameter   : Node_Index;
      Children    : Natural;
   begin
      Item := Make (Void);
      if Body_Block = No_Node then
         Fail (State);
         return;
      end if;
      Close_Paren := Before (First_Token (State, Tree, Body_Block));
      Open_Function (State, Natural (Value.Line));
      Consume (State, First_Token (State, Tree, Node));
      if Is_Method then
         New_Local (State, Self_Name (State), Ignored_Index);
         Adjust_Locals (State, 1);
      end if;
      if Parameters /= No_Node then
         for Position in 1 .. Get (Tree, Parameters).List_Length loop
            pragma Loop_Invariant (Count <= Natural (Position) - 1);
            Parameter := List_Item (Tree, Parameters, Position);
            Consume (State, First_Token (State, Tree, Parameter));
            New_Local (State, Get (Tree, Parameter).Symbol, Ignored_Index);
            Count := Count + 1;
            exit when Failed (State) or else Count > 255;
         end loop;
      end if;
      Adjust_Locals (State, Count);
      Facts := Current (State);
      Facts.Facts.Parameter_Count := Bytecode.Byte (Natural'Min (Facts.Active, 255));
      Set_Current (State, Facts);
      if Value.Is_Vararg then
         Consume (State, Before (Close_Paren));
         Set_Vararg (State, Facts.Active);
      end if;
      Reserve_Registers (State, Facts.Active);
      Consume (State, Close_Paren);
      Statement_List (State, Result, Tree, Symbols, Body_Block, 1);
      Consume (State, Last_Token (State, Tree, Node));
      Close_Function (State, Result, Natural (Token_Line (State, Last_Token (State, Tree, Node))));
      if Failed (State) then
         return;
      end if;
      --  [puc lparser.c:codeclosure] in the enclosing function: the new prototype is its
      --  last child.
      Children := Child_Count (State);
      if Children = 0 then
         Fail (State);
         return;
      end if;
      Code_ABx (State, Closure, 0, Children - 1, Position);
      Item := Make (Relocatable, Position);
      To_Next_Register (State, Item);
   end Function_Body_Of;

   ---------------------------------------------------------------------------------------------
   --  Statements

   procedure Statement_Of
     (State : in out Compiler_State; Result : in out Chunk; Tree : Syntax_Tree;
      Symbols : Symbol_Table; Node : Node_Index)
   with
     Pre                => Ready (Result, Tree, Symbols, Node),
     Post               => Is_Well_Formed (Result),
     Subprogram_Variant => (Decreases => Node, Decreases => 20);

   --  [puc lparser.c:block] Block Node in a block of its own.
   procedure Block_Of
     (State : in out Compiler_State; Result : in out Chunk; Tree : Syntax_Tree;
      Symbols : Symbol_Table; Node : Node_Index)
   with
     Pre                => Ready (Result, Tree, Symbols, Node),
     Post               => Is_Well_Formed (Result),
     Subprogram_Variant => (Decreases => Node, Decreases => 17)
   is
   begin
      Enter_Block (State, False);
      Statement_List (State, Result, Tree, Symbols, Node, 1);
      Leave_Block (State);
   end Block_Of;

   --  [puc lparser.c:statlist] The statements of Block Node from From on; then the token read
   --  last is the last of the block (its last statement, or a ';' after it).
   procedure Statement_List
     (State : in out Compiler_State; Result : in out Chunk; Tree : Syntax_Tree;
      Symbols : Symbol_Table; Node : Node_Index; From : List_Index)
   is
   begin
      for Position in List_Index'Max (From, 1) .. Get (Tree, Node).List_Length loop
         pragma Loop_Invariant (Is_Well_Formed (Result));
         exit when Failed (State);
         Statement_Of (State, Result, Tree, Symbols, List_Item (Tree, Node, Position));
      end loop;
      Consume (State, Last_Token (State, Tree, Node));
   end Statement_List;

   --  [puc lparser.c:forbody].
   procedure For_Body
     (State : in out Compiler_State; Result : in out Chunk; Tree : Syntax_Tree;
      Symbols : Symbol_Table; Node : Node_Index; Base : Natural; Line : Line_Number;
      Variables : Natural; Is_Generic : Boolean; Do_Token : Natural)
   with
     Pre                => Ready (Result, Tree, Symbols, Node),
     Post               => Is_Well_Formed (Result),
     Subprogram_Variant => (Decreases => Node, Decreases => 18)
   is
      Prepare : Natural;
      Loop_At : Natural;
      Here    : Natural;
      Ignored : Natural;
   begin
      Consume (State, Do_Token);
      Code_ABx (State, (if Is_Generic then Generic_For_Prepare else For_Prepare), Base, 0,
                Prepare);
      Enter_Block (State, False);
      Adjust_Locals (State, Variables);
      Reserve_Registers (State, Variables);
      Block_Of (State, Result, Tree, Symbols, Node);
      Leave_Block (State);
      Get_Label (State, Here);
      Fix_For_Jump (State, Prepare, Here, False);
      if Is_Generic then
         Code_ABC (State, Generic_For_Call, Base, 0, Variables, False, Ignored);
         Fix_Line (State, Line);
      end if;
      Code_ABx (State, (if Is_Generic then Generic_For_Loop else For_Loop), Base, 0, Loop_At);
      Fix_For_Jump (State, Loop_At, After (Prepare), True);
      Fix_Line (State, Line);
   end For_Body;

   --  [puc lparser.c:test_then_block] Clause Node of an if statement; Has_Following is whether
   --  an elseif or else follows it.
   procedure Test_Then_Block
     (State : in out Compiler_State; Result : in out Chunk; Tree : Syntax_Tree;
      Symbols : Symbol_Table; Node : Node_Index; Escape : in out Jump_List;
      Has_Following : Boolean)
   with
     Pre                => Ready (Result, Tree, Symbols, Node),
     Post               => Is_Well_Formed (Result),
     Subprogram_Variant => (Decreases => Node, Decreases => 19)
   is
      Condition  : constant Node_Index := Child (Tree, Node, 1);
      Body_Block : constant Node_Index := Child (Tree, Node, 2);
      Item       : Expression;
      Then_Token : Natural;
      First      : Node_Index;
      False_Jump : Jump_List;
      From       : List_Index := 1;
      Jump_At    : Jump_List;
   begin
      if Condition = No_Node or else Body_Block = No_Node then
         Fail (State);
         return;
      end if;
      Consume (State, Before (First_Token (State, Tree, Condition)));
      Expression_Of (State, Result, Tree, Symbols, Condition, Item);
      Then_Token := After (Last_Token (State, Tree, Condition));
      Consume (State, Then_Token);
      First := (if Get (Tree, Body_Block).List_Length > 0
                then List_Item (Tree, Body_Block, 1) else No_Node);
      if First /= No_Node and then Kind_Of (Tree, First) = Break_Statement
        and then First_Token (State, Tree, First) = After (Then_Token)
      then
         --  'if x then break': the jump out of the loop is the test's jump.
         Go_If_False (State, Item);
         Consume (State, After (Then_Token));
         Enter_Block (State, False);
         New_Goto
           (State, Break_Name (State), Token_Line (State, After (Then_Token)), Item.True_List);
         if Get (Tree, Body_Block).List_Length = 1 then
            Consume (State, Last_Token (State, Tree, Body_Block));
            Leave_Block (State);
            return;
         end if;
         Consume (State, Before (First_Token (State, Tree, List_Item (Tree, Body_Block, 2))));
         Jump (State, False_Jump);
         From := 2;
      else
         Go_If_True (State, Item);
         Enter_Block (State, False);
         False_Jump := Item.False_List;
      end if;
      Statement_List (State, Result, Tree, Symbols, Body_Block, From);
      Leave_Block (State);
      if Has_Following then
         Jump (State, Jump_At);
         Concatenate_Jumps (State, Escape, Jump_At);
      end if;
      Patch_To_Here (State, False_Jump);
   end Test_Then_Block;

   --  [puc lparser.c:check_conflict] Target, a variable assigned after the targets on the
   --  stack from First on, must not change a table or index they use first.
   procedure Check_Conflict
     (State : in out Compiler_State; First : Natural; Target : Expression)
   is
      Extra    : constant Natural := Current (State).Free_Register;
      Conflict : Boolean := False;
      Previous : Expression;
      Ignored  : Natural;
   begin
      for Position in Natural'Min (First, 2 ** 28) + 1 .. Targets_Length (State) loop
         Previous := Target_At (State, Position);
         if Is_Indexed (Previous) then
            if Previous.Kind = Indexed_Upvalue then
               if Target.Kind = Upvalue_Slot and then Previous.Table = Target.Info then
                  Conflict := True;
                  Previous.Kind := Indexed_String;
                  Previous.Table := Extra;
               end if;
            else
               if Target.Kind = Local_Register and then Previous.Table = Target.Register then
                  Conflict := True;
                  Previous.Table := Extra;
               end if;
               if Previous.Kind = Indexed_Register and then Target.Kind = Local_Register
                 and then Previous.Key = Target.Register
               then
                  Conflict := True;
                  Previous.Key := Extra;
               end if;
            end if;
            Set_Target (State, Position, Previous);
         end if;
      end loop;
      if Conflict then
         if Target.Kind = Local_Register then
            Code_ABC (State, Move, Extra, Target.Register, 0, False, Ignored);
         else
            Code_ABC (State, Get_Upvalue, Extra, Target.Info, 0, False, Ignored);
         end if;
         Reserve_Registers (State, 1);
      end if;
   end Check_Conflict;

   --  [puc lparser.c:exprstat, restassign].
   procedure Assignment_Of
     (State : in out Compiler_State; Result : in out Chunk; Tree : Syntax_Tree;
      Symbols : Symbol_Table; Node : Node_Index)
   with
     Pre                => Ready (Result, Tree, Symbols, Node),
     Post               => Is_Well_Formed (Result),
     Subprogram_Variant => (Decreases => Node, Decreases => 19)
   is
      Targets  : constant Node_Index := Child (Tree, Node, 1);
      Values   : constant Node_Index := Child (Tree, Node, 2);
      Base     : constant Natural := Targets_Length (State);
      Target   : Node_Index;
      Variable : Node_Index;
      Item     : Expression;
      Value    : Expression;
      Count    : Natural := 0;
      Values_Count : Natural;
      Success  : Boolean := True;
   begin
      if Targets = No_Node or else Values = No_Node then
         Fail (State);
         return;
      end if;
      for Position in 1 .. Get (Tree, Targets).List_Length loop
         pragma Loop_Invariant (Is_Well_Formed (Result));
         pragma Loop_Invariant (Count <= Natural (Position) - 1);
         Target := List_Item (Tree, Targets, Position);
         Variable := Child (Tree, Target, 1);
         if Variable = No_Node then
            Fail (State);
            return;
         end if;
         Suffixed_Expression_Of (State, Result, Tree, Symbols, Variable, Item);
         if Count > 0 and then not Is_Indexed (Item) then
            Check_Conflict (State, Base, Item);
         end if;
         Push_Target (State, Item, Success);
         exit when not Success or else Failed (State);
         Count := Count + 1;
      end loop;
      if not Success then
         Raise_Error (State, Not_Enough_Memory, 0);
      end if;
      if Failed (State) or else Count = 0
        or else Targets_Length (State) /= Base + Count
      then
         Fail (State);
         return;
      end if;
      Consume (State, After (Last_Token (State, Tree, Targets)));
      Expression_List_Of (State, Result, Tree, Symbols, Values, Value, Values_Count);
      if Targets_Length (State) /= Base + Count then
         Fail (State);
         return;
      end if;
      if Values_Count /= Count then
         declare
            Unused_Copy : Expression := Value;
         begin
            Adjust_Assign (State, Count, Values_Count, Unused_Copy);
         end;
         Value := Make (Fixed_Register, Natural'Max (Current (State).Free_Register, 1) - 1);
      else
         Set_One_Return (State, Value);
      end if;
      declare
         Unused_Copy : Expression := Value;
      begin
         Store_Variable
           (State, Target_At (State, Base + Count),
            Unused_Copy);
      end;
      for Position in reverse Base + 1 .. Base + Count - 1 loop
         exit when Failed (State);
         declare
            Unused_Copy : Expression :=
              Make (Fixed_Register, Natural'Max (Current (State).Free_Register, 1) - 1);
         begin
            Store_Variable
              (State, Target_At (State, Position),
               Unused_Copy);
         end;
      end loop;
      Truncate_Targets (State, Base);
   end Assignment_Of;

   --  [puc lparser.c:localstat].
   procedure Local_Statement_Of
     (State : in out Compiler_State; Result : in out Chunk; Tree : Syntax_Tree;
      Symbols : Symbol_Table; Node : Node_Index)
   with
     Pre                => Ready (Result, Tree, Symbols, Node),
     Post               => Is_Well_Formed (Result),
     Subprogram_Variant => (Decreases => Node, Decreases => 19)
   is
      Names    : constant Node_Index := Child (Tree, Node, 1);
      Values   : constant Node_Index := Child (Tree, Node, 2);
      Name     : Node_Index;
      Index    : Natural := 0;
      Count    : Natural := 0;
      To_Close : Integer := -1;
      Item     : Expression := Make (Void);
      Values_Count : Natural := 0;
      Value    : Constant_Value;
      Constant_Known : Boolean := False;
      Kind     : Variable_Kind;
      Ignored  : Natural;
   begin
      if Names = No_Node then
         Fail (State);
         return;
      end if;
      for Position in 1 .. Get (Tree, Names).List_Length loop
         pragma Loop_Invariant (Count <= Natural (Position) - 1);
         Name := List_Item (Tree, Names, Position);
         Consume (State, First_Token (State, Tree, Name));
         New_Local (State, Get (Tree, Name).Symbol, Index);
         exit when Failed (State);
         Kind := (case Get (Tree, Name).Attribute is
                    when Regular => Regular_Variable,
                    when Constant_Attribute => Constant_Variable,
                    when Close_Attribute => Close_Variable);
         Set_Variable (State, Index, Kind, (others => <>));
         if Kind = Close_Variable then
            To_Close := Current (State).Active + Count;
         end if;
         Count := Count + 1;
         exit when Count > 255;
      end loop;
      Consume (State, Last_Token (State, Tree, Names));
      if Values /= No_Node then
         Consume (State, After (Last_Token (State, Tree, Names)));
         Expression_List_Of (State, Result, Tree, Symbols, Values, Item, Values_Count);
      end if;
      if Failed (State) then
         return;
      end if;
      if Count = Values_Count and then Local_Variable_Of (State, Index).Kind = Constant_Variable
      then
         To_Constant (State, Item, Value, Constant_Known);
      end if;
      if Constant_Known and then Count > 0 then
         Set_Variable (State, Index, Compile_Time_Variable, Value);
         Adjust_Locals (State, Count - 1);
         Activate_Constant (State);
      else
         declare
            Unused_Copy : Expression := Item;
         begin
            Adjust_Assign (State, Count, Values_Count, Unused_Copy);
         end;
         Adjust_Locals (State, Count);
      end if;
      if To_Close >= 0 then
         Mark_To_Be_Closed (State);
         Code_ABC (State, To_Be_Closed, Register_Level (State, To_Close), 0, 0, False, Ignored);
      end if;
   end Local_Statement_Of;

   --  [puc lparser.c:repeatstat].
   procedure Repeat_Of
     (State : in out Compiler_State; Result : in out Chunk; Tree : Syntax_Tree;
      Symbols : Symbol_Table; Node : Node_Index)
   with
     Pre                => Ready (Result, Tree, Symbols, Node),
     Post               => Is_Well_Formed (Result),
     Subprogram_Variant => (Decreases => Node, Decreases => 19)
   is
      Body_Block : constant Node_Index := Child (Tree, Node, 1);
      Condition  : constant Node_Index := Child (Tree, Node, 2);
      Start      : Natural;
      Item       : Expression;
      Exit_List  : Jump_List;
      Normal     : Jump_List;
      Upvalue    : Boolean;
      Ignored    : Natural;
   begin
      if Body_Block = No_Node or else Condition = No_Node then
         Fail (State);
         return;
      end if;
      Get_Label (State, Start);
      Enter_Block (State, True);
      Enter_Block (State, False);
      Consume (State, First_Token (State, Tree, Node));
      Statement_List (State, Result, Tree, Symbols, Body_Block, 1);
      Consume (State, After (Last_Token (State, Tree, Body_Block)));
      Expression_Of (State, Result, Tree, Symbols, Condition, Item);
      if Item.Kind = Nil_Value then
         Item.Kind := False_Value;
      end if;
      Go_If_True (State, Item);
      Exit_List := Item.False_List;
      Upvalue := Block_Has_Upvalue (State);
      Leave_Block (State);
      if Upvalue then
         Jump (State, Normal);
         Patch_To_Here (State, Exit_List);
         Code_ABC (State, Close, Variables_On_Stack (State), 0, 0, False, Ignored);
         Jump (State, Exit_List);
         Patch_To_Here (State, Normal);
      end if;
      Patch_List (State, Exit_List, Start);
      Leave_Block (State);
   end Repeat_Of;

   --  [puc lparser.c:forstat, fornum, forlist].
   procedure For_Of
     (State : in out Compiler_State; Result : in out Chunk; Tree : Syntax_Tree;
      Symbols : Symbol_Table; Node : Node_Index)
   with
     Pre                => Ready (Result, Tree, Symbols, Node),
     Post               => Is_Well_Formed (Result),
     Subprogram_Variant => (Decreases => Node, Decreases => 19)
   is
      Value       : constant Syntax_Trees.Node := Get (Tree, Node);
      Names       : constant Node_Index := Child (Tree, Node, 1);
      Expressions : constant Node_Index := Child (Tree, Node, 2);
      Body_Block  : constant Node_Index := Child (Tree, Node, 3);
      For_Token   : constant Natural := First_Token (State, Tree, Node);
      Line        : Line_Number := Token_Line (State, For_Token);
      Base        : Natural;
      Ignored_Index : Natural;
      Count       : Natural := 0;
      Item        : Expression;
      Values      : Natural;
      Name        : Node_Index;
      Element     : Node_Index;
   begin
      if Names = No_Node or else Expressions = No_Node or else Body_Block = No_Node then
         Fail (State);
         return;
      end if;
      Enter_Block (State, True);
      Base := Current (State).Free_Register;
      if Value.Kind = Numeric_For then
         Consume (State, After (For_Token));
         for Step in 1 .. 3 loop
            New_Local (State, For_State_Name (State), Ignored_Index);
         end loop;
         New_Local (State, Get (Tree, Names).Symbol, Ignored_Index);
         if Get (Tree, Expressions).List_Length not in 2 .. 3 then
            Fail (State);
            return;
         end if;
         for Position in 1 .. Get (Tree, Expressions).List_Length loop
            pragma Loop_Invariant (Is_Well_Formed (Result));
            Element := List_Item (Tree, Expressions, Position);
            Consume (State, Before (First_Token (State, Tree, Element)));
            Expression_Of (State, Result, Tree, Symbols, Element, Item);
            declare
               Unused_Copy : Expression := Item;
            begin
               To_Next_Register (State, Unused_Copy);
            end;
         end loop;
         if Get (Tree, Expressions).List_Length = 2 then
            Load_Integer (State, Current (State).Free_Register, 1);
            Reserve_Registers (State, 1);
         end if;
         Adjust_Locals (State, 3);
         For_Body (State, Result, Tree, Symbols, Body_Block, Base, Line, 1, False,
                   After (Last_Token (State, Tree, Expressions)));
      else
         if Get (Tree, Names).List_Length = 0 then
            Fail (State);
            return;
         end if;
         Name := List_Item (Tree, Names, 1);
         Consume (State, First_Token (State, Tree, Name));
         for Step in 1 .. 4 loop
            New_Local (State, For_State_Name (State), Ignored_Index);
         end loop;
         for Position in 1 .. Get (Tree, Names).List_Length loop
            pragma Loop_Invariant (Count <= Natural (Position) - 1);
            Name := List_Item (Tree, Names, Position);
            Consume (State, First_Token (State, Tree, Name));
            New_Local (State, Get (Tree, Name).Symbol, Ignored_Index);
            Count := Count + 1;
            exit when Failed (State) or else Count > 255;
         end loop;
         Consume (State, After (Last_Token (State, Tree, Names)));
         Line := Token_Line (State, After (After (Last_Token (State, Tree, Names))));
         Expression_List_Of (State, Result, Tree, Symbols, Expressions, Item, Values);
         declare
            Unused_Item : Expression := Item;
         begin
            Adjust_Assign (State, 4, Values, Unused_Item);
         end;
         Adjust_Locals (State, 4);
         Mark_To_Be_Closed (State);
         Check_Stack (State, 3);
         For_Body (State, Result, Tree, Symbols, Body_Block, Base, Line, Count, True,
                   After (Last_Token (State, Tree, Expressions)));
      end if;
      Consume (State, Last_Token (State, Tree, Node));
      Leave_Block (State);
   end For_Of;

   --  [puc lparser.c:retstat].
   procedure Return_Of
     (State : in out Compiler_State; Result : in out Chunk; Tree : Syntax_Tree;
      Symbols : Symbol_Table; Node : Node_Index)
   with
     Pre                => Ready (Result, Tree, Symbols, Node),
     Post               => Is_Well_Formed (Result),
     Subprogram_Variant => (Decreases => Node, Decreases => 19)
   is
      Values : constant Node_Index := Child (Tree, Node, 1);
      First  : Natural := Variables_On_Stack (State);
      Count  : Integer := 0;
      Values_Count : Natural;
      Item   : Expression;
      Call_Item : Instruction;
   begin
      Consume (State, First_Token (State, Tree, Node));
      if Values /= No_Node and then Get (Tree, Values).List_Length > 0 then
         Expression_List_Of (State, Result, Tree, Symbols, Values, Item, Values_Count);
         Count := Values_Count;
         if Has_Multiple_Results (Item) then
            Set_Returns (State, Item, Multiple_Results);
            if Item.Kind = Open_Call and then Count = 1 and then not Inside_To_Be_Closed (State)
            then
               Call_Item := Get (State, Item.Info);
               Call_Item.Operation := Tail_Call;
               Put (State, Item.Info, Call_Item);
            end if;
            Count := Multiple_Results;
         elsif Count = 1 then
            declare
               Unused_Copy : Expression := Item;
            begin
               To_Any_Register (State, Unused_Copy, First);
            end;
         else
            declare
               Unused_Copy : Expression := Item;
            begin
               To_Next_Register (State, Unused_Copy);
            end;
         end if;
      end if;
      Return_Values (State, First, Count);
   end Return_Of;

   --  [puc lparser.c:gotostat].
   procedure Goto_Of (State : in out Compiler_State; Tree : Syntax_Tree; Node : Node_Index)
   with Pre => Is_Well_Formed (Tree) and then Node in 1 .. Node_Count (Tree)
   is
      Name_At : constant Natural := After (First_Token (State, Tree, Node));
      Label   : Label_Entry;
      Found   : Boolean;
      Level   : Natural;
      Jump_At : Jump_List;
      Ignored : Natural;
   begin
      Consume (State, Name_At);
      Find_Label (State, Get (Tree, Node).Symbol, Label, Found);
      if not Found then
         Jump (State, Jump_At);
         New_Goto (State, Get (Tree, Node).Symbol, Token_Line (State, Name_At), Jump_At);
      else
         Level := Register_Level (State, Label.Active);
         if Variables_On_Stack (State) > Level then
            Code_ABC (State, Close, Level, 0, 0, False, Ignored);
         end if;
         Jump (State, Jump_At);
         Patch_List (State, Jump_At, Natural'Max (Label.PC, 0));
      end if;
   end Goto_Of;

   --  [puc lparser.c:statement].
   procedure Statement_Of
     (State : in out Compiler_State; Result : in out Chunk; Tree : Syntax_Tree;
      Symbols : Symbol_Table; Node : Node_Index)
   is
      Value   : constant Syntax_Trees.Node := Get (Tree, Node);
      First   : constant Node_Index := Child (Tree, Node, 1);
      Second  : constant Node_Index := Child (Tree, Node, 2);
      Item    : Expression;
      Other   : Expression;
      Unused_Item : Expression;
      Ignored_Index : Natural;
      Start   : Natural;
      Exit_At : Jump_List;
      Jump_At : Jump_List;
      Escape  : Jump_List := No_Jump;
      Ignored : Boolean;
      Instruction_Item : Instruction;
      Clause  : Node_Index;
   begin
      case Value.Kind is
         when Local_Statement =>
            Local_Statement_Of (State, Result, Tree, Symbols, Node);
         when Local_Function =>
            if First = No_Node or else Second = No_Node then
               Fail (State);
               return;
            end if;
            Start := Current (State).Active;
            Consume (State, First_Token (State, Tree, First));
            New_Local (State, Get (Tree, First).Symbol, Ignored_Index);
            Adjust_Locals (State, 1);
            Function_Body_Of (State, Result, Tree, Symbols, Second, False, Unused_Item);
            Set_Debug_Start (State, Local_Variable_Of (State, Start).Debug_Index, PC (State));
         when Function_Statement =>
            if First = No_Node or else Second = No_Node then
               Fail (State);
               return;
            end if;
            Consume (State, First_Token (State, Tree, Node));
            Suffixed_Expression_Of (State, Result, Tree, Symbols, First, Item);
            Function_Body_Of
              (State, Result, Tree, Symbols, Second, Get (Tree, Second).Is_Method, Other);
            declare
               Unused_Copy : Expression := Other;
            begin
               Store_Variable (State, Item, Unused_Copy);
            end;
            Fix_Line (State, Token_Line (State, First_Token (State, Tree, Node)));
         when Assignment =>
            Assignment_Of (State, Result, Tree, Symbols, Node);
         when Call_Statement =>
            if First = No_Node then
               Fail (State);
               return;
            end if;
            Suffixed_Expression_Of (State, Result, Tree, Symbols, First, Item);
            if Item.Kind /= Open_Call then
               Fail (State);
               return;
            end if;
            Instruction_Item := Get (State, Item.Info);
            Instruction_Item.C := 1;
            Put (State, Item.Info, Instruction_Item);
         when Do_Statement =>
            if First = No_Node then
               Fail (State);
               return;
            end if;
            Consume (State, First_Token (State, Tree, Node));
            Block_Of (State, Result, Tree, Symbols, First);
         when While_Statement =>
            if First = No_Node or else Second = No_Node then
               Fail (State);
               return;
            end if;
            Consume (State, First_Token (State, Tree, Node));
            Get_Label (State, Start);
            Expression_Of (State, Result, Tree, Symbols, First, Item);
            if Item.Kind = Nil_Value then
               Item.Kind := False_Value;
            end if;
            Go_If_True (State, Item);
            Exit_At := Item.False_List;
            Enter_Block (State, True);
            Consume (State, After (Last_Token (State, Tree, First)));
            Block_Of (State, Result, Tree, Symbols, Second);
            Jump (State, Jump_At);
            Patch_List (State, Jump_At, Start);
            Consume (State, Last_Token (State, Tree, Node));
            Leave_Block (State);
            Patch_To_Here (State, Exit_At);
         when Repeat_Statement =>
            Repeat_Of (State, Result, Tree, Symbols, Node);
         when If_Statement =>
            for Position in 1 .. Value.List_Length loop
               pragma Loop_Invariant (Is_Well_Formed (Result));
               exit when Failed (State);
               Clause := List_Item (Tree, Node, Position);
               Test_Then_Block
                 (State, Result, Tree, Symbols, Clause, Escape,
                  Position < Value.List_Length or else First /= No_Node);
            end loop;
            if First /= No_Node then
               Consume (State, Before (First_Token (State, Tree, First)));
               Block_Of (State, Result, Tree, Symbols, First);
            end if;
            Consume (State, Last_Token (State, Tree, Node));
            Patch_To_Here (State, Escape);
         when Numeric_For | Generic_For =>
            For_Of (State, Result, Tree, Symbols, Node);
         when Return_Statement =>
            Return_Of (State, Result, Tree, Symbols, Node);
         when Break_Statement =>
            Consume (State, First_Token (State, Tree, Node));
            Jump (State, Jump_At);
            New_Goto (State, Break_Name (State),
                      Token_Line (State, First_Token (State, Tree, Node)), Jump_At);
         when Goto_Statement =>
            Goto_Of (State, Tree, Node);
         when Label_Statement =>
            --  [puc lparser.c:labelstat] The labels right after it are declared first.
            for Position in 1 .. Value.List_Length loop
               pragma Loop_Invariant (Is_Well_Formed (Result));
               exit when Failed (State);
               Statement_Of (State, Result, Tree, Symbols, List_Item (Tree, Node, Position));
            end loop;
            Consume (State, (if Value.Check_Point.Ordinal > 0
                             then Natural (Value.Check_Point.Ordinal) - 1 else 0));
            Create_Label (State, Value.Symbol, Value.Line, Value.Is_Last_Label, Ignored);
         when others =>
            Fail (State);
      end case;
      if not Failed (State) then
         Set_Free_Register (State, Variables_On_Stack (State));
      end if;
   end Statement_Of;

   ---------------------------------------------------------------------------------------------
   --  The chunk

   --  The symbol of Text, interned in Symbols.
   procedure Name_Of
     (Symbols : in out Symbol_Table; Budget : in out Memory_Budget; Text : String;
      Symbol : out Symbol_Index)
   with
     Pre  => Is_Valid (Symbols) and then Text'Length in 1 .. 20,
     Post => Is_Valid (Symbols) and then Limit (Budget) = Limit (Budget)'Old
   is
      Buffer  : Character_Arrays.Growable_Array;
      Success : Boolean := True;
   begin
      Symbol := No_Symbol;
      for Byte of Text loop
         pragma Loop_Invariant (Limit (Budget) = Limit (Budget)'Loop_Entry);
         Character_Arrays.Append (Buffer, Byte, Budget, Success);
         exit when not Success;
      end loop;
      if Success and then Character_Arrays.Length (Buffer) > 0 then
         Intern (Symbols, Budget, Buffer, 1, Character_Arrays.Length (Buffer), Symbol);
      end if;
      Character_Arrays.Clear (Buffer, Budget);
      pragma Assert (Character_Arrays.Is_Released (Buffer));
   end Name_Of;

   --  The names the compiler makes up, interned in Symbols.
   procedure Intern_Names
     (Symbols : in out Symbol_Table;
      Budget  : in out Memory_Budget;
      Environment, Break, Self, For_State : out Symbol_Index)
   with
     Pre  => Is_Valid (Symbols),
     Post => Is_Valid (Symbols) and then Limit (Budget) = Limit (Budget)'Old
   is
   begin
      Name_Of (Symbols, Budget, "_ENV", Environment);
      Name_Of (Symbols, Budget, "break", Break);
      Name_Of (Symbols, Budget, "self", Self);
      Name_Of (Symbols, Budget, "(for state)", For_State);
   end Intern_Names;

   --  Fills in the place and "near" part of Item, an error PUC Lua raises at token Ordinal
   --  ([puc llex.c:luaX_syntaxerror]), by reading the chunk again up to it.
   procedure Describe_Token
     (Source : Sources.Source; Symbols : in out Symbol_Table; Budget : in out Memory_Budget;
      Ordinal : Natural; Item : in out Diagnostic)
   with
     Pre  => Is_Valid (Symbols),
     Post => Is_Valid (Symbols) and then Limit (Budget) = Limit (Budget)'Old
   is
      Lexer   : Pyro.Lexer.Lexer_State;
      Current : Token;
   begin
      Pyro.Lexer.Start (Lexer, Source, Budget);
      for Step in 0 .. Source.Length + 1 loop
         pragma Loop_Invariant (Is_Valid (Symbols));
         pragma Loop_Invariant (Pyro.Lexer.Is_Valid (Lexer, Source));
         pragma Loop_Invariant (Limit (Budget) = Limit (Budget)'Loop_Entry);
         exit when Pyro.Lexer.Failed (Lexer);
         Pyro.Lexer.Next_Token (Lexer, Source, Symbols, Budget, Current);
         if Natural (Current.Ordinal) >= Ordinal or else Current.Kind = End_Of_Stream then
            Item.Has_Place := True;
            Item.Place := (First => Current.First, Last => Current.Last);
            Item.Found := Current.Kind;
            Item.Found_Byte := Current.Byte;
            Item.Lua_Line := Pyro.Lexer.Line (Lexer);
            if Current.Kind in Token_With_Text then
               Item.Near := Near_Text;
               Pyro.Lexer.Token_Text (Lexer, Symbols, Budget, Item.Near_Text);
            else
               Item.Near := Near_Token;
               Item.Near_Token := Current.Kind;
               Item.Near_Byte := Current.Byte;
            end if;
            exit;
         end if;
      end loop;
      Pyro.Lexer.Clear (Lexer, Budget);
      pragma Assert (Pyro.Lexer.Is_Released (Lexer));
   end Describe_Token;

   --  [puc lparser.c:mainfunc] Compiles the main function into Result.
   procedure Compile_Main
     (State : in out Compiler_State; Result : in out Chunk; Tree : Syntax_Tree;
      Symbols : Symbol_Table; Root : Node_Index)
   with
     Pre  =>
       Is_Well_Formed (Tree)
       and then Root <= Node_Count (Tree)
       and then Is_Valid (Symbols)
       and then Is_Well_Formed (Result),
     Post => Is_Well_Formed (Result)
   is
      Body_Block : constant Node_Index :=
        (if Root in 1 .. Node_Count (Tree) then Child (Tree, Root, 2) else No_Node);
   begin
      if Body_Block = No_Node then
         Fail (State);
         return;
      end if;
      Open_Function (State, 0);
      Set_Vararg (State, 0);
      Set_Environment_Upvalue (State);
      Statement_List (State, Result, Tree, Symbols, Body_Block, 1);
      Close_Function (State, Result, 0);
   end Compile_Main;

   --  Appends State's error to Problems: a compile-time limit as PUC Lua reports it, or an
   --  internal error.
   procedure Report_Error
     (State    : in out Compiler_State;
      Source   : Sources.Source;
      Symbols  : in out Symbol_Table;
      Problems : in out Diagnostic_Lists.Growable_Array)
   with Pre => Is_Valid (Symbols), Post => Is_Valid (Symbols)
   is
      Error           : Diagnostic := (What => Internal_Error, others => <>);
      Budget          : Memory_Budget := Budget_Of (State);
      Ignored_Success : Boolean;
   begin
      if Has_Error (State) then
         Error := Error_Of (State);
         if Error.What /= Not_Enough_Memory then
            Describe_Token
              (Source, Symbols, Budget, Natural (Error.Detection.Ordinal), Error);
         else
            Error.Has_Lua_Line := False;
         end if;
      end if;
      if Diagnostics.Names_Exist (Error, Symbols) then
         Diagnostic_Lists.Append (Problems, Error, Budget, Ignored_Success);
      end if;
      Set_Budget (State, Budget);
   end Report_Error;

   procedure Compile
     (Source   : Sources.Source;
      Tree     : Syntax_Tree;
      Root     : Node_Index;
      Symbols  : in out Symbol_Table;
      Budget   : in out Memory_Budget;
      Problems : in out Diagnostic_Lists.Growable_Array;
      Result   : in out Chunk)
   is
      State           : Compiler_State;
      Valid           : Boolean;
      Limit_Before    : constant Byte_Count := Limit (Budget);
      Working         : Memory_Budget := Budget;
      Environment, Break, Self, For_State : Symbol_Index;
      Ignored_Success : Boolean;
   begin
      Clear (Result, Working);
      Intern_Names (Symbols, Working, Environment, Break, Self, For_State);
      Set_Budget (State, Working);
      Set_Names (State, Environment, Break, Self, For_State);
      Read_Tokens (State, Source, Symbols);
      if not Failed (State) then
         Compile_Main (State, Result, Tree, Symbols, Root);
      end if;
      Working := Budget_Of (State);
      if Failed (State) then
         Clear (Result, Working);
         Set_Budget (State, Working);
         Report_Error (State, Source, Symbols, Problems);
      else
         --  Every prototype returned is checked: an internal error otherwise.
         Validate (Result, Working, Valid);
         Set_Budget (State, Working);
         if not Valid then
            Make_Internal_Error (State);
            Report_Error (State, Source, Symbols, Problems);
         end if;
      end if;
      Release (State);
      --  The memory still in use is the chunk's, charged to the caller's budget.
      Budget := Create (Limit_Before);
      Charge (Budget, Byte_Count'Min (Used (Budget_Of (State)), Limit_Before), Ignored_Success);
   end Compile;

end Pyro.Compiler;
