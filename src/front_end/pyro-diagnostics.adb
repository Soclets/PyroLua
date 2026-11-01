--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  Diagnostics: what went wrong in a chunk, recorded for both the rich and the Lua-style report.

package body Pyro.Diagnostics with SPARK_Mode => On is

   procedure Append
     (Output : in out Character_Arrays.Growable_Array;
      Budget : in out Memory_Budget;
      Text   : String)
   is
      Success : Boolean;
   begin
      for Byte of Text loop
         pragma Loop_Invariant (Limit (Budget) = Limit (Budget)'Loop_Entry);
         Character_Arrays.Append (Output, Byte, Budget, Success);
         exit when not Success;
      end loop;
   end Append;

   function Image (Value : Natural) return String is
      Result    : String (1 .. 10) := [others => '0'];
      First     : Positive := 10;
      Remaining : Natural := Value;
   begin
      for Position in reverse 1 .. 10 loop
         pragma Loop_Invariant (First in Position .. 10);
         Result (Position) := Character'Val (Character'Pos ('0') + Remaining mod 10);
         First := Position;
         Remaining := Remaining / 10;
         exit when Remaining = 0;
      end loop;
      declare
         Count   : constant Positive := 11 - First;
         Shifted : String (1 .. 10) := [others => '0'];
      begin
         for Index in 1 .. Count loop
            Shifted (Index) := Result (First + Index - 1);
         end loop;
         return Shifted (1 .. Count);
      end;
   end Image;

   --  Appends the symbol's bytes.
   procedure Append_Symbol
     (Output : in out Character_Arrays.Growable_Array;
      Budget : in out Memory_Budget;
      Table  : Symbol_Table;
      Symbol : Symbol_Index)
   with
     Pre  => Is_Valid (Table) and then Symbol <= Count (Table),
     Post => Limit (Budget) = Limit (Budget)'Old
   is
   begin
      if Symbol /= No_Symbol then
         Append (Output, Budget, Text (Table, Symbol));
      end if;
   end Append_Symbol;

   --  [puc llex.c:luaX_token2str] How PUC Lua names a token in a message.
   procedure Append_Token
     (Output : in out Character_Arrays.Growable_Array;
      Budget : in out Memory_Budget;
      Kind   : Token_Kind;
      Byte   : Character)
   with Post => Limit (Budget) = Limit (Budget)'Old
   is
   begin
      if Kind = Other_Byte then
         if Byte in ' ' .. '~' then
            Append (Output, Budget, "'" & Byte & "'");
         else
            Append (Output, Budget, "'<\" & Image (Character'Pos (Byte)) & ">'");
         end if;
      elsif Kind in End_Of_Stream | Token_With_Text then
         Append (Output, Budget, Spelling (Kind));
      else
         Append (Output, Budget, "'" & Spelling (Kind) & "'");
      end if;
   end Append_Token;

   procedure Append_Lua_Message
     (Output : in out Character_Arrays.Growable_Array;
      Budget : in out Memory_Budget;
      Item   : Diagnostic;
      Table  : Symbol_Table;
      Source : Sources.Source)
   is
      Other : constant String := Image (Natural (Item.Other_Line));
   begin
      if Item.Has_Lua_Line then
         Append (Output, Budget, Chunk_Id (Source) & ":" & Image (Natural (Item.Lua_Line)) & ": ");
      end if;
      case Item.What is
         when Malformed_Number => Append (Output, Budget, "malformed number");
         when Unfinished_String => Append (Output, Budget, "unfinished string");
         when Unfinished_Long_String =>
            Append (Output, Budget, "unfinished long string (starting at line " & Other & ")");
         when Unfinished_Long_Comment =>
            Append (Output, Budget, "unfinished long comment (starting at line " & Other & ")");
         when Invalid_Long_String_Delimiter =>
            Append (Output, Budget, "invalid long string delimiter");
         when Hexadecimal_Digit_Expected => Append (Output, Budget, "hexadecimal digit expected");
         when Missing_Opening_Brace => Append (Output, Budget, "missing '{'");
         when Missing_Closing_Brace => Append (Output, Budget, "missing '}'");
         when UTF_8_Value_Too_Large => Append (Output, Budget, "UTF-8 value too large");
         when Decimal_Escape_Too_Large => Append (Output, Budget, "decimal escape too large");
         when Invalid_Escape_Sequence => Append (Output, Budget, "invalid escape sequence");
         when Token_Expected =>
            Append_Token (Output, Budget, Item.Expected, ASCII.NUL);
            Append (Output, Budget, " expected");
         when Token_Expected_To_Close =>
            Append_Token (Output, Budget, Item.Expected, ASCII.NUL);
            Append (Output, Budget, " expected (to close ");
            Append_Token (Output, Budget, Item.Opener, ASCII.NUL);
            Append (Output, Budget, " at line " & Other & ")");
         when Unexpected_Symbol => Append (Output, Budget, "unexpected symbol");
         when Not_A_Statement | Not_Assignable => Append (Output, Budget, "syntax error");
         when Function_Arguments_Expected =>
            Append (Output, Budget, "function arguments expected");
         when Name_Or_Vararg_Expected => Append (Output, Budget, "<name> or '...' expected");
         when Equals_Or_In_Expected => Append (Output, Budget, "'=' or 'in' expected");
         when Nesting_Too_Deep => Append (Output, Budget, "C stack overflow");
         when Vararg_Outside_Vararg_Function =>
            Append (Output, Budget, "cannot use '...' outside a vararg function");
         when Unknown_Attribute =>
            Append (Output, Budget, "unknown attribute '");
            Append_Symbol (Output, Budget, Table, Item.Name);
            Append (Output, Budget, "'");
         when Multiple_To_Be_Closed =>
            Append (Output, Budget, "multiple to-be-closed variables in local list");
         when Assignment_To_Constant =>
            Append (Output, Budget, "attempt to assign to const variable '");
            Append_Symbol (Output, Budget, Table, Item.Name);
            Append (Output, Budget, "'");
         when Label_Already_Defined =>
            Append (Output, Budget, "label '");
            Append_Symbol (Output, Budget, Table, Item.Name);
            Append (Output, Budget, "' already defined on line " & Other);
         when Goto_Into_Scope =>
            Append (Output, Budget, "<goto ");
            Append_Symbol (Output, Budget, Table, Item.Name);
            Append (Output, Budget, "> at line " & Other & " jumps into the scope of local '");
            Append_Symbol (Output, Budget, Table, Item.Other_Name);
            Append (Output, Budget, "'");
         when Break_Outside_Loop =>
            Append (Output, Budget, "break outside loop at line " & Other);
         when No_Visible_Label =>
            Append (Output, Budget, "no visible label '");
            Append_Symbol (Output, Budget, Table, Item.Name);
            Append (Output, Budget, "' for <goto> at line " & Other);
         when Too_Many_Registers =>
            Append (Output, Budget, "function or expression needs too many registers");
         when Too_Many_Local_Variables | Too_Many_Upvalues =>
            --  [puc lparser.c:errorlimit]
            Append (Output, Budget,
                    (if Item.What = Too_Many_Upvalues then "too many upvalues (limit is 255) in "
                     else "too many local variables (limit is 200) in "));
            if Item.In_Main_Function then
               Append (Output, Budget, "main function");
            else
               Append (Output, Budget, "function at line " & Other);
            end if;
         when Control_Structure_Too_Long =>
            Append (Output, Budget, "control structure too long");
         when Not_Enough_Memory => Append (Output, Budget, "not enough memory");
         when Binary_Chunk =>
            --  [differs] Precompiled chunks are not loaded.
            Append (Output, Budget, "precompiled chunks are not supported");
         when Internal_Error =>
            Append (Output, Budget, "internal error: the compiler built invalid bytecode");
      end case;
      case Item.Near is
         when No_Near => null;
         when Near_Token =>
            --  [puc llex.c:lexerror] A NUL byte is token 0, "no token": no "near" part.
            if Item.Near_Token /= Other_Byte or else Item.Near_Byte /= ASCII.NUL then
               Append (Output, Budget, " near ");
               Append_Token (Output, Budget, Item.Near_Token, Item.Near_Byte);
            end if;
         when Near_Text =>
            Append (Output, Budget, " near '");
            Append_Symbol (Output, Budget, Table, Item.Near_Text);
            Append (Output, Budget, "'");
      end case;
   end Append_Lua_Message;

end Pyro.Diagnostics;
