--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  The host functions of the pyrolua program: the small fixed set test scripts use.

--  [trusted] Ordinary Ada around the machine's host-function protocol (docs/PROOFS.md, cli/).
pragma SPARK_Mode (Off);

with GNAT.OS_Lib;
with Interfaces;
with Pyro.Integer_Arithmetic;
with Pyro.Tables;
with Pyro.Values; use Pyro.Values;

package body Host_Functions is

   use Pyro.Virtual_Machine;
   use type Interfaces.Unsigned_64;
   use type Interfaces.Integer_64;
   use type Pyro.Tables.Set_Status;
   use type Pyro.Tables.Next_Status;

   --  The host functions, in the order of their numbers. Ipairs_Iterator is not a global.
   type Function_Name is
     (Print_Function, Type_Function, Tostring_Function, Select_Function, Error_Function,
      Assert_Function, Pcall_Function, Setmetatable_Function, Getmetatable_Function,
      Rawget_Function, Rawset_Function, Rawequal_Function, Rawlen_Function, Next_Function,
      Pairs_Function, Ipairs_Function, Ipairs_Iterator);

   subtype Global_Function is Function_Name range Print_Function .. Ipairs_Function;

   function Lua_Name (Name : Function_Name) return String
   is (case Name is
         when Print_Function        => "print",
         when Type_Function         => "type",
         when Tostring_Function     => "tostring",
         when Select_Function       => "select",
         when Error_Function        => "error",
         when Assert_Function       => "assert",
         when Pcall_Function        => "pcall",
         when Setmetatable_Function => "setmetatable",
         when Getmetatable_Function => "getmetatable",
         when Rawget_Function       => "rawget",
         when Rawset_Function       => "rawset",
         when Rawequal_Function     => "rawequal",
         when Rawlen_Function       => "rawlen",
         when Next_Function         => "next",
         when Pairs_Function        => "pairs",
         when Ipairs_Function       => "ipairs",
         when Ipairs_Iterator       => "for iterator");

   function Id_Of (Name : Function_Name) return Host_Id
   is (Host_Id (Function_Name'Pos (Name) + 1));

   --  [puc lvm.c:MAXTAGLOOP] The longest chain of __index tables ipairs follows.
   Maximum_Tag_Loop : constant := 2_000;

   --  What print writes, before Flush.
   Output      : String (1 .. 65_536);
   Output_Last : Natural := 0;

   procedure Write (Text : String) is
   begin
      if Output_Last + Text'Length > Output'Last then
         Flush;
      end if;
      if Text'Length > Output'Length then
         declare
            Written : Integer;
            pragma Unreferenced (Written);
         begin
            Written := GNAT.OS_Lib.Write (GNAT.OS_Lib.Standout, Text'Address, Text'Length);
         end;
         return;
      end if;
      Output (Output_Last + 1 .. Output_Last + Text'Length) := Text;
      Output_Last := Output_Last + Text'Length;
   end Write;

   procedure Flush is
      Written : Integer;
      pragma Unreferenced (Written);
   begin
      if Output_Last > 0 then
         Written := GNAT.OS_Lib.Write (GNAT.OS_Lib.Standout, Output'Address, Output_Last);
         Output_Last := 0;
      end if;
   end Flush;

   procedure Register_All
     (M       : in out Machine;
      Budget  : in out Pyro.Memory_Budgets.Memory_Budget;
      Success : out Boolean) is
   begin
      for Name in Global_Function loop
         Register (M, Budget, Lua_Name (Name), Id_Of (Name), Success);
         exit when not Success;
      end loop;
   end Register_All;

   --  A made-up address for an object, as tostring prints one ("0x" and 14 hex digits).
   function Address (Item : Value) return String is
      Digits_Text : constant String := "0123456789abcdef";
      Result      : String (1 .. 16) := "0x" & [1 .. 14 => '0'];
      Remaining   : Interfaces.Unsigned_64 :=
        16#5555_0000_0000# + 64 * Interfaces.Unsigned_64 (Item.Object);
   begin
      for Position in reverse 3 .. Result'Last loop
         Result (Position) := Digits_Text (Natural (Remaining mod 16) + 1);
         Remaining := Remaining / 16;
      end loop;
      return Result;
   end Address;

   --  [puc lauxlib.c:luaL_typeerror] The type name of Item in a message: its metatable's
   --  __name when that is a string.
   function Kind_Name (M : Machine; Item : Value) return String is
      Name : constant Value := Metafield (M, Item, Name_Field);
   begin
      if Is_String (M, Name) then
         return String_Text (M, Name);
      end if;
      return Type_Name (M, Item);
   end Kind_Name;

   --  [puc lauxlib.c:luaL_tolstring] Item as tostring writes it, when it has no __tostring.
   function Image (M : Machine; Item : Value) return String is
   begin
      if Item.Kind /= Object_Value then
         return Basic_Image (Item);
      elsif Is_String (M, Item) then
         return String_Text (M, Item);
      end if;
      return Kind_Name (M, Item) & ": " & Address (Item);
   end Image;

   function Truthy (Item : Value) return Boolean
   is (Item.Kind /= Nil_Value and then Item /= Boolean_Value_Of (False));

   procedure Answer (M : in out Machine; Budget : in out Pyro.Memory_Budgets.Memory_Budget) is
      Name  : constant Function_Name := Function_Name'Val (Natural (Host_Function (M)) - 1);
      Count : constant Natural := Argument_Count (M);
      Step  : constant Natural := Continuation (M);

      --  [puc lauxlib.c:pushglobalfuncname] The global variable holding the waiting host
      --  function, or "?". (Lua looks through package.loaded, where _G is the only table to
      --  hold these functions.)
      function Global_Name return String is
         Table  : constant Value := Globals (M);
         Self   : constant Value := Called_Function (M);
         Key    : Value := Nil;
         Found  : Value;
         Item   : Value;
         Status : Pyro.Tables.Next_Status;
      begin
         if not Is_Table (M, Table) then
            return "?";
         end if;
         loop
            Next_Pair (M, Table, Key, Found, Item, Status);
            exit when Status /= Pyro.Tables.Found;
            if Is_String (M, Found) and then Raw_Equal (Item, Self) then
               return String_Text (M, Found);
            end if;
            Key := Found;
         end loop;
         return "?";
      end Global_Name;

      --  [puc lauxlib.c:luaL_argerror] The function is named as it was called; a method does
      --  not count its self argument.
      procedure Argument_Error (Number : Positive; Problem : String) is
         Called   : constant String := Host_Call_Name (M);
         Position : Natural := Number;
      begin
         if Host_Called_As_Method (M) then
            Position := Position - 1;
            if Position = 0 then
               Raise_Message
                 (M, Budget, "calling '" & Called & "' on bad self (" & Problem & ")", 1);
               return;
            end if;
         end if;
         Raise_Message
           (M, Budget,
            "bad argument #" & Pyro.Integer_Arithmetic.Image (Interfaces.Integer_64 (Position))
            & " to '" & (if Called = "" then Global_Name else Called) & "' (" & Problem & ")",
            1);
      end Argument_Error;

      --  [puc lauxlib.c:luaL_typeerror]
      procedure Type_Error (Number : Positive; Expected : String) is
      begin
         Argument_Error
           (Number,
            Expected & " expected, got "
            & (if Number > Count then "no value" else Kind_Name (M, Argument (M, Number))));
      end Type_Error;

      function Arguments (First : Positive) return Value_List is
         Result : Value_List (1 .. Natural'Max (0, Count - First + 1));
      begin
         for Index in Result'Range loop
            Result (Index) := Argument (M, First + Index - 1);
         end loop;
         return Result;
      end Arguments;

      --  Returns Text as a string.
      procedure Return_Text (Text : String) is
         Item    : Value;
         Success : Boolean;
      begin
         New_String (M, Budget, Text, Item, Success);
         if not Success then
            Raise_Message (M, Budget, "not enough memory", 0);
            return;
         end if;
         Return_Values (M, Budget, [1 => Item]);
      end Return_Text;

      --  [puc lauxlib.c:luaL_tolstring] Converts argument Position for print or tostring:
      --  calls its __tostring with continuation Position (True), or gives its text.
      --  Called is also True when it raised "not enough memory".
      procedure Convert (Position : Positive; Called : out Boolean; Text : out Value) is
         Item    : constant Value := Argument (M, Position);
         Handler : constant Value := Metafield (M, Item, To_String_Field);
         Success : Boolean;
      begin
         Called := False;
         Text := Item;
         if Handler /= Nil then
            Call (M, Budget, Handler, [1 => Item], Position, Protect => False);
            Called := True;
         elsif not Is_String (M, Item) then
            New_String (M, Budget, Image (M, Item), Text, Success);
            if not Success then
               Raise_Message (M, Budget, "not enough memory", 0);
               Called := True;
            end if;
         end if;
      end Convert;

      --  The result of a __tostring call: it must be a string or a number (lua_isstring), and
      --  a number becomes its text.
      procedure Converted (Valid : out Boolean; Text : out Value) is
         Success : Boolean;
      begin
         Text := Result (M, 1);
         Valid := Is_String (M, Text) or else Text.Kind in Integer_Value | Float_Value;
         if not Valid then
            Raise_Message (M, Budget, "'__tostring' must return a string", 1);
         elsif not Is_String (M, Text) then
            New_String (M, Budget, Basic_Image (Text), Text, Success);
            if not Success then
               Valid := False;
               Raise_Message (M, Budget, "not enough memory", 0);
            end if;
         end if;
      end Converted;

      Text    : Value;
      Success : Boolean;
      Called  : Boolean;
   begin
      case Name is
         when Print_Function =>
            --  The continuation is the argument whose __tostring returned.
            declare
               First : Positive := 1;
               Valid : Boolean;
            begin
               if Step > 0 then
                  Converted (Valid, Text);
                  if not Valid then
                     return;
                  end if;
                  if Step > 1 then
                     Write ([1 => ASCII.HT]);
                  end if;
                  Write (String_Text (M, Text));
                  First := Step + 1;
               end if;
               for Index in First .. Count loop
                  Convert (Index, Called, Text);
                  if Called then
                     return;
                  end if;
                  if Index > 1 then
                     Write ([1 => ASCII.HT]);
                  end if;
                  Write (String_Text (M, Text));
               end loop;
            end;
            Write ([1 => ASCII.LF]);
            Return_Values (M, Budget, []);

         when Type_Function =>
            if Count = 0 then
               Argument_Error (1, "value expected");
               return;
            end if;
            Return_Text (Type_Name (M, Argument (M, 1)));

         when Tostring_Function =>
            if Step > 0 then
               declare
                  Valid : Boolean;
               begin
                  Converted (Valid, Text);
                  if Valid then
                     Return_Values (M, Budget, [1 => Text]);
                  end if;
               end;
               return;
            end if;
            if Count = 0 then
               Argument_Error (1, "value expected");
               return;
            end if;
            Convert (1, Called, Text);
            if not Called then
               Return_Values (M, Budget, [1 => Text]);
            end if;

         when Select_Function =>
            declare
               Selector : constant Value := Argument (M, 1);
               Number   : Interfaces.Integer_64;
            begin
               if Is_String (M, Selector) and then String_Text (M, Selector) = "#" then
                  Return_Values
                    (M, Budget,
                     [1 => Integer_Value_Of (Interfaces.Integer_64 (Count - 1))]);
                  return;
               elsif Selector.Kind /= Integer_Value then
                  Type_Error (1, "number");
                  return;
               end if;
               --  [puc lbaselib.c:luaB_select] Counting the selector as argument 1.
               Number := Pyro.Integer_Arithmetic.To_Signed (Selector.Bits);
               if Number < 0 then
                  Number := Interfaces.Integer_64 (Count) + Number;
               elsif Number > Interfaces.Integer_64 (Count) then
                  Number := Interfaces.Integer_64 (Count);
               end if;
               if Number < 1 then
                  Argument_Error (1, "index out of range");
                  return;
               end if;
               Return_Values (M, Budget, Arguments (Natural (Number) + 1));
            end;

         when Error_Function =>
            declare
               Error : constant Value := Argument (M, 1);
               Level : Interfaces.Integer_64 := 1;
            begin
               if Count >= 2 and then Argument (M, 2).Kind = Integer_Value then
                  Level := Pyro.Integer_Arithmetic.To_Signed (Argument (M, 2).Bits);
               end if;
               if Is_String (M, Error) and then Level > 0 then
                  Raise_Message (M, Budget, String_Text (M, Error), Natural (Level));
               else
                  Raise_Error (M, Budget, Error);
               end if;
            end;

         when Assert_Function =>
            if Count = 0 then
               Argument_Error (1, "value expected");
            elsif Truthy (Argument (M, 1)) then
               Return_Values (M, Budget, Arguments (1));
            elsif Count >= 2 then
               Raise_Error (M, Budget, Argument (M, 2));
            else
               Raise_Message (M, Budget, "assertion failed!", 1);
            end if;

         when Pcall_Function =>
            case Step is
               when 0 =>
                  if Count = 0 then
                     Argument_Error (1, "value expected");
                     return;
                  end if;
                  Call (M, Budget, Argument (M, 1), Arguments (2), 1, Protect => True);
               when others =>
                  if Call_Succeeded (M) then
                     declare
                        Results : Value_List (1 .. Result_Count (M) + 1);
                     begin
                        Results (1) := Boolean_Value_Of (True);
                        for Index in 2 .. Results'Last loop
                           Results (Index) := Result (M, Index - 1);
                        end loop;
                        Return_Values (M, Budget, Results);
                     end;
                  else
                     Return_Values (M, Budget, [Boolean_Value_Of (False), Result (M, 1)]);
                  end if;
            end case;

         when Setmetatable_Function =>
            declare
               T     : constant Value := Argument (M, 1);
               Table : constant Value := Argument (M, 2);
            begin
               if not Is_Table (M, T) then
                  Type_Error (1, "table");
               elsif Count < 2 or else not (Table.Kind = Nil_Value or else Is_Table (M, Table))
               then
                  Type_Error (2, "nil or table");
               elsif Metafield (M, T, Metatable_Field) /= Nil then
                  Raise_Message (M, Budget, "cannot change a protected metatable", 1);
               else
                  Set_Metatable (M, T, Table);
                  Return_Values (M, Budget, [1 => T]);
               end if;
            end;

         when Getmetatable_Function =>
            if Count = 0 then
               Argument_Error (1, "value expected");
            elsif Metafield (M, Argument (M, 1), Metatable_Field) /= Nil then
               Return_Values (M, Budget, [1 => Metafield (M, Argument (M, 1), Metatable_Field)]);
            else
               Return_Values (M, Budget, [1 => Metatable (M, Argument (M, 1))]);
            end if;

         when Rawget_Function =>
            if not Is_Table (M, Argument (M, 1)) then
               Type_Error (1, "table");
            elsif Count < 2 then
               Argument_Error (2, "value expected");
            else
               Return_Values (M, Budget, [1 => Raw_Index (M, Argument (M, 1), Argument (M, 2))]);
            end if;

         when Rawset_Function =>
            if not Is_Table (M, Argument (M, 1)) then
               Type_Error (1, "table");
            elsif Count < 2 then
               Argument_Error (2, "value expected");
            elsif Count < 3 then
               Argument_Error (3, "value expected");
            else
               declare
                  Status : Pyro.Tables.Set_Status;
               begin
                  Raw_Store
                    (M, Budget, Argument (M, 1), Argument (M, 2), Argument (M, 3), Status);
                  case Status is
                     when Pyro.Tables.Done =>
                        Return_Values (M, Budget, [1 => Argument (M, 1)]);
                     when Pyro.Tables.Invalid_Key =>
                        Raise_Message
                          (M, Budget,
                           (if Argument (M, 2).Kind = Nil_Value then "table index is nil"
                            else "table index is NaN"), 0);
                     when Pyro.Tables.Out_Of_Memory =>
                        Raise_Message (M, Budget, "not enough memory", 0);
                  end case;
               end;
            end if;

         when Rawequal_Function =>
            if Count < 1 then
               Argument_Error (1, "value expected");
            elsif Count < 2 then
               Argument_Error (2, "value expected");
            else
               Return_Values
                 (M, Budget,
                  [1 => Boolean_Value_Of (Raw_Equal (Argument (M, 1), Argument (M, 2)))]);
            end if;

         when Rawlen_Function =>
            if not (Is_Table (M, Argument (M, 1)) or else Is_String (M, Argument (M, 1))) then
               Type_Error (1, "table or string");
            else
               Return_Values
                 (M, Budget, [1 => Integer_Value_Of (Raw_Length (M, Argument (M, 1)))]);
            end if;

         when Next_Function =>
            if not Is_Table (M, Argument (M, 1)) then
               Type_Error (1, "table");
               return;
            end if;
            declare
               Key, Item : Value;
               Status    : Pyro.Tables.Next_Status;
            begin
               Next_Pair (M, Argument (M, 1), Argument (M, 2), Key, Item, Status);
               case Status is
                  when Pyro.Tables.Found =>
                     Return_Values (M, Budget, [Key, Item]);
                  when Pyro.Tables.Finished =>
                     Return_Values (M, Budget, [1 => Nil]);
                  when Pyro.Tables.Invalid_Key =>
                     Raise_Message (M, Budget, "invalid key to 'next'", 0);
               end case;
            end;

         when Pairs_Function =>
            if Step > 0 then
               --  [puc lbaselib.c:luaB_pairs] What __pairs returned, three values.
               Return_Values (M, Budget, [Result (M, 1), Result (M, 2), Result (M, 3)]);
               return;
            end if;
            if Count = 0 then
               Argument_Error (1, "value expected");
            elsif Metafield (M, Argument (M, 1), Pairs_Field) /= Nil then
               Call
                 (M, Budget, Metafield (M, Argument (M, 1), Pairs_Field),
                  [1 => Argument (M, 1)], 1, Protect => False);
            else
               New_Function (M, Budget, Id_Of (Next_Function), Text, Success);
               if Success then
                  Return_Values (M, Budget, [Text, Argument (M, 1), Nil]);
               else
                  Raise_Message (M, Budget, "not enough memory", 0);
               end if;
            end if;

         when Ipairs_Function =>
            if Count = 0 then
               Argument_Error (1, "value expected");
            else
               New_Function (M, Budget, Id_Of (Ipairs_Iterator), Text, Success);
               if Success then
                  Return_Values (M, Budget, [Text, Argument (M, 1), Integer_Value_Of (0)]);
               else
                  Raise_Message (M, Budget, "not enough memory", 0);
               end if;
            end if;

         when Ipairs_Iterator =>
            --  [puc lbaselib.c:ipairsaux] t[i + 1], through __index (lua_geti).
            declare
               Index : constant Interfaces.Integer_64 :=
                 (if Argument (M, 2).Kind = Integer_Value
                  then Pyro.Integer_Arithmetic.Add (Integer_Of (Argument (M, 2)), 1)
                  else 1);
               Key     : constant Value := Integer_Value_Of (Index);
               T       : Value := Argument (M, 1);
               Item    : Value := Nil;
               Handler : Value;
            begin
               if Step > 0 then
                  Item := Result (M, 1);
               else
                  for Loop_Count in 1 .. Maximum_Tag_Loop loop
                     if Is_Table (M, T) then
                        Item := Raw_Index (M, T, Key);
                        exit when Item /= Nil;
                        Handler := Metafield (M, T, Index_Event);
                        exit when Handler = Nil;
                     else
                        Handler := Metafield (M, T, Index_Event);
                        if Handler = Nil then
                           Raise_Message
                             (M, Budget,
                              "attempt to index a " & Type_Name (M, T) & " value", 0);
                           return;
                        end if;
                     end if;
                     if Is_Function (M, Handler) then
                        Call (M, Budget, Handler, [T, Key], 1, Protect => False);
                        return;
                     end if;
                     T := Handler;
                  end loop;
               end if;
               if Item.Kind = Nil_Value then
                  Return_Values (M, Budget, [1 => Nil]);
               else
                  Return_Values (M, Budget, [Key, Item]);
               end if;
            end;
      end case;
   end Answer;

end Host_Functions;
