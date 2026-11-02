--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  Unit tests of the runtime (heap, strings, tables, collector): what pyrolua cannot reach
--  before the virtual machine exists. Prints each failure and exits with status 1 if any.

with Ada.Command_Line;
with Ada.Text_IO;          use Ada.Text_IO;
with Interfaces;           use Interfaces;
with Pyro.Heap;            use Pyro.Heap;
with Pyro.Strings;
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

   --  SipHash against the reference vectors: key 00 .. 0F, message 00 .. N - 1 (SipHash-2-4
   --  as published; SipHash-1-3 from the same reference code, checked against them).
   procedure Test_Hash is
      Key : constant Pyro.Strings.Seed :=
        (K0 => 16#0706_0504_0302_0100#, K1 => 16#0F0E_0D0C_0B0A_0908#);
      type Vector is record
         Length       : Natural;
         Sip_24       : Unsigned_64;
         Sip_13       : Unsigned_64;
      end record;
      Vectors : constant array (Positive range <>) of Vector :=
        [(0, 16#726f_db47_dd0e_0e31#, 16#abac_0158_050f_c4dc#),
         (1, 16#74f8_39c5_93dc_67fd#, 16#c9f4_9bf3_7d57_ca93#),
         (2, 16#0d6c_8009_d9a9_4f5a#, 16#82cb_9b02_4dc7_d44d#),
         (7, 16#ab02_00f5_8b01_d137#, 16#d392_7d98_9bb1_1140#),
         (8, 16#93f5_f579_9a93_2462#, 16#3690_9511_8d29_9a8e#),
         (15, 16#a129_ca61_49be_45e5#, 16#d320_d86d_2a51_9956#),
         (63, 16#958a_324c_eb06_4572#, 16#9d19_9062_b7bb_b3a8#)];
   begin
      for V of Vectors loop
         declare
            Data : Byte_Array (1 .. Pyro.Byte_Position'Base (V.Length));
         begin
            for Index in Data'Range loop
               Data (Index) := Character'Val (Integer (Index) - 1);
            end loop;
            Check (Pyro.Strings.Sip_Hash (Key, Data, 2, 4) = V.Sip_24,
                   "hash: SipHash-2-4 of" & Natural'Image (V.Length) & " bytes");
            Check (Pyro.Strings.Hash (Key, Data) = V.Sip_13,
                   "hash: SipHash-1-3 of" & Natural'Image (V.Length) & " bytes");
         end;
      end loop;
      Check (Pyro.Strings.Hash_Words (Key, 1, 2) = 16#6c63_0018_434b_d4cc#,
             "hash: words 1 and 2");
      Check (Pyro.Strings.Hash (Key, Bytes ("hello")) = 16#b6be_2b8c_d613_85b7#,
             "hash: hello");
   end Test_Hash;

   --  Equal bytes give the same string, under every rebuild of the intern set.
   procedure Test_Interning is
      H        : Heap;
      Budget   : Memory_Budget := Create (Default_Limit);
      Key      : constant Pyro.Strings.Seed := (K0 => 16#1234#, K1 => 16#5678#);
      A, B, C  : Object_Handle;
      First    : array (1 .. 5_000) of Object_Handle;
      Again    : Object_Handle;
      Same     : Boolean := True;
   begin
      Set_Seed (H, Key);
      New_String (H, Budget, Bytes ("abc"), A);
      New_String (H, Budget, Bytes ("abc"), B);
      New_String (H, Budget, Bytes ("abd"), C);
      Check (A /= No_Object and then A = B, "interning: equal bytes, same string");
      Check (C /= A, "interning: other bytes, other string");
      Check (String_Hash (H, A) = Pyro.Strings.Hash (Key, Bytes ("abc")),
             "interning: hash under the seed");
      for Index in First'Range loop
         New_String (H, Budget, Bytes ("s" & Integer'Image (Index)), First (Index));
      end loop;
      for Index in First'Range loop
         New_String (H, Budget, Bytes ("s" & Integer'Image (Index)), Again);
         Same := Same and then Again = First (Index) and then Again /= No_Object;
      end loop;
      Check (Same, "interning: 5000 strings found again after rebuilds");
      Check (Slot_Count (H) = 5_002, "interning: one slot per distinct string");
      Clear (H, Budget);
      Check (Used (Budget) = 0, "interning: Clear releases the intern set");
   end Test_Interning;

begin
   Test_Heap_Strings;
   Test_Heap_Many;
   Test_Hash;
   Test_Interning;
   if Failures > 0 then
      Put_Line (Natural'Image (Failures) & " failure(s)");
      Ada.Command_Line.Set_Exit_Status (1);
   end if;
end Runtime_Test;
