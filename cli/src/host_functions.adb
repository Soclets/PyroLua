--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  The host functions of the pyrolua program: the small fixed set test scripts use.

--  [trusted] Ordinary Ada around the machine's host-function protocol (docs/PROOFS.md, cli/).
pragma SPARK_Mode (Off);

with GNAT.OS_Lib;
with Interfaces;
with Pyro.Integer_Arithmetic;
with Pyro.Values; use Pyro.Values;

package body Host_Functions is

   use Pyro.Virtual_Machine;
   use type Interfaces.Unsigned_64;
   use type Interfaces.Integer_64;

   --  The host functions, in the order of their numbers.
   type Function_Name is
     (Print_Function, Type_Function, Tostring_Function, Select_Function, Error_Function,
      Assert_Function, Pcall_Function);

   function Lua_Name (Name : Function_Name) return String
   is (case Name is
         when Print_Function    => "print",
         when Type_Function     => "type",
         when Tostring_Function => "tostring",
         when Select_Function   => "select",
         when Error_Function    => "error",
         when Assert_Function   => "assert",
         when Pcall_Function    => "pcall");

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
      for Name in Function_Name loop
         Register (M, Budget, Lua_Name (Name), Host_Id (Function_Name'Pos (Name) + 1), Success);
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

   --  [puc lauxlib.c:luaL_tolstring] Item as tostring writes it (no metamethods yet).
   function Image (M : Machine; Item : Value) return String is
   begin
      if Item.Kind /= Object_Value then
         return Basic_Image (Item);
      elsif Is_String (M, Item) then
         return String_Text (M, Item);
      end if;
      return Type_Name (M, Item) & ": " & Address (Item);
   end Image;

   function Truthy (Item : Value) return Boolean
   is (Item.Kind /= Nil_Value and then Item /= Boolean_Value_Of (False));

   procedure Answer (M : in out Machine; Budget : in out Pyro.Memory_Budgets.Memory_Budget) is
      Name  : constant Function_Name := Function_Name'Val (Natural (Host_Function (M)) - 1);
      Count : constant Natural := Argument_Count (M);

      --  [puc lauxlib.c:luaL_argerror]
      procedure Argument_Error (Number : Positive; Problem : String) is
      begin
         Raise_Message
           (M, Budget,
            "bad argument #" & Pyro.Integer_Arithmetic.Image (Interfaces.Integer_64 (Number))
            & " to '" & Lua_Name (Name) & "' (" & Problem & ")", 1);
      end Argument_Error;

      function Arguments (First : Positive) return Value_List is
         Result : Value_List (1 .. Natural'Max (0, Count - First + 1));
      begin
         for Index in Result'Range loop
            Result (Index) := Argument (M, First + Index - 1);
         end loop;
         return Result;
      end Arguments;

      Text    : Value;
      Success : Boolean;
   begin
      case Name is
         when Print_Function =>
            for Index in 1 .. Count loop
               if Index > 1 then
                  Write ([1 => ASCII.HT]);
               end if;
               Write (Image (M, Argument (M, Index)));
            end loop;
            Write ([1 => ASCII.LF]);
            Return_Values (M, Budget, []);

         when Type_Function =>
            if Count = 0 then
               Argument_Error (1, "value expected");
               return;
            end if;
            New_String (M, Budget, Type_Name (M, Argument (M, 1)), Text, Success);
            Return_Values (M, Budget, [1 => Text]);

         when Tostring_Function =>
            if Count = 0 then
               Argument_Error (1, "value expected");
               return;
            end if;
            if Is_String (M, Argument (M, 1)) then
               Return_Values (M, Budget, [1 => Argument (M, 1)]);
            else
               New_String (M, Budget, Image (M, Argument (M, 1)), Text, Success);
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
                  Argument_Error (1, "number expected, got " & Type_Name (M, Selector));
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
            case Continuation (M) is
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
      end case;
   end Answer;

end Host_Functions;
