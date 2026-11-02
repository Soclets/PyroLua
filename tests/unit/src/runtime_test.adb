--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  Unit tests of the runtime (heap, strings, tables, collector): what pyrolua cannot reach
--  before the virtual machine exists. Prints each failure and exits with status 1 if any.

with Ada.Command_Line;
with Ada.Text_IO;          use Ada.Text_IO;
with Pyro.Heap;            use Pyro.Heap;
with Pyro.Memory_Budgets;  use Pyro.Memory_Budgets;
with Pyro.Values;          use Pyro.Values;

procedure Runtime_Test is

   Failures : Natural := 0;

   procedure Check (Condition : Boolean; What : String) is
   begin
      if not Condition then
         Failures := Failures + 1;
         Put_Line ("FAIL: " & What);
      end if;
   end Check;

   function Bytes (Text : String) return Byte_Array is
      Result : Byte_Array (1 .. Text'Length);
   begin
      for Index in Text'Range loop
         Result (Pyro.Byte_Position (Index - Text'First + 1)) := Text (Index);
      end loop;
      return Result;
   end Bytes;

   --  Strings are allocated, read back, and freed by Clear with their memory.
   procedure Test_Heap_Strings is
      H      : Heap;
      Budget : Memory_Budget := Create (Default_Limit);
      A, B   : Object_Handle;
      Empty  : Object_Handle;
   begin
      New_String (H, Budget, Bytes ("hello"), A);
      New_String (H, Budget, Bytes ("a" & ASCII.NUL & "b"), B);
      New_String (H, Budget, Bytes (""), Empty);
      Check (A /= No_Object and then B /= No_Object and then Empty /= No_Object,
             "heap: strings allocated");
      Check (Kind_Of (H, A) = String_Object and then Kind_Of (H, Empty) = String_Object,
             "heap: string kinds");
      Check (String_Length (H, A) = 5 and then String_Length (H, B) = 3
             and then String_Length (H, Empty) = 0, "heap: string lengths");
      Check (String_Byte (H, A, 1) = 'h' and then String_Byte (H, A, 5) = 'o'
             and then String_Byte (H, B, 2) = ASCII.NUL, "heap: string bytes");
      Check (Kind_Of (H, Slot_Count (H) + 1) = Free_Object, "heap: past the last slot");
      Clear (H, Budget);
      Check (Used (Budget) = 0, "heap: Clear releases everything");
   end Test_Heap_Strings;

   --  Enough strings to fill several chunks, then a budget too small for one more.
   procedure Test_Heap_Many is
      H      : Heap;
      Budget : Memory_Budget := Create (Default_Limit);
      S      : Object_Handle;
      Made   : Natural := 0;
   begin
      for Count in 1 .. 10_000 loop
         New_String (H, Budget, Bytes (Integer'Image (Count)), S);
         if S /= No_Object and then Kind_Of (H, S) = String_Object then
            Made := Made + 1;
         end if;
      end loop;
      Check (Made = 10_000 and then Slot_Count (H) = 10_000, "heap: 10000 strings");
      Clear (H, Budget);
      Check (Used (Budget) = 0, "heap: Clear releases 10000 strings");
      Budget := Create (100);
      New_String (H, Budget, Bytes ("too much for the budget"), S);
      Check (S = No_Object and then Used (Budget) = 0, "heap: out of budget is a result");
      Clear (H, Budget);
   end Test_Heap_Many;

begin
   Test_Heap_Strings;
   Test_Heap_Many;
   if Failures > 0 then
      Put_Line (Natural'Image (Failures) & " failure(s)");
      Ada.Command_Line.Set_Exit_Status (1);
   end if;
end Runtime_Test;
