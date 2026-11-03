--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  Unit tests of the runtime (heap, strings, tables, collector): what pyrolua cannot reach
--  before the virtual machine exists. Prints each failure and exits with status 1 if any.

with Ada.Command_Line;
with Ada.Containers.Ordered_Maps;
with Ada.Text_IO;          use Ada.Text_IO;
with Interfaces;           use Interfaces;
with Pyro.Floats;
with Pyro.Garbage_Collector;
with Pyro.Integer_Arithmetic;
with Pyro.Heap;            use Pyro.Heap;
with Pyro.Strings;
with Pyro.Tables;          use Pyro.Tables;
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

   --  Numbers are written as Lua writes them (lobject.c's tostringbuff).
   procedure Test_Number_Images is
      use Pyro.Floats;
      function Integer_Image (Value : Integer_64) return String
      renames Pyro.Integer_Arithmetic.Image;
      Zero : constant Float_Bits := From_Integer (0);
      One  : constant Float_Bits := From_Integer (1);
   begin
      Check (Integer_Image (0) = "0" and then Integer_Image (-1) = "-1"
             and then Integer_Image (1234) = "1234",
             "images: small integers");
      Check (Integer_Image (Integer_64'Last) = "9223372036854775807"
             and then Integer_Image (Integer_64'First) = "-9223372036854775808",
             "images: integer limits");
      Check (Pyro.Floats.Image (One) = "1.0" and then Pyro.Floats.Image (Zero) = "0.0",
             "images: integral floats end in .0");
      Check (Pyro.Floats.Image (Arithmetic (Negate, Zero, Zero)) = "-0.0", "images: -0.0");
      Check (Pyro.Floats.Image (Arithmetic (Divide, One, From_Integer (10))) = "0.1",
             "images: 0.1");
      Check (Pyro.Floats.Image (Arithmetic (Power, From_Integer (10), From_Integer (15)))
             = "1e+15", "images: 1e+15");
      Check (Pyro.Floats.Image (Arithmetic (Power, From_Integer (2), From_Integer (63)))
             = "9.2233720368548e+18", "images: 2^63");
      Check (Pyro.Floats.Image (Arithmetic (Divide, One, Zero)) = "inf"
             and then Pyro.Floats.Image (Arithmetic (Divide, From_Integer (-1), Zero)) = "-inf",
             "images: infinities");
      Check (Pyro.Floats.Image (Arithmetic (Divide, Zero, Zero)) in "nan" | "-nan",
             "images: NaN");
   end Test_Number_Images;

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

   --  A reference map for tables: plain Ada, keyed by the normalized key.
   function Less (Left, Right : Value) return Boolean
   is (Value_Kind'Pos (Left.Kind) < Value_Kind'Pos (Right.Kind)
       or else (Left.Kind = Right.Kind
                and then (Left.Bits < Right.Bits
                          or else (Left.Bits = Right.Bits and then Left.Object < Right.Object))));

   package Reference_Maps is new Ada.Containers.Ordered_Maps
     (Key_Type => Value, Element_Type => Value, "<" => Less);

   --  A deterministic pseudo-random sequence (xorshift).
   Random_State : Unsigned_64 := 16#9E37_79B9_7F4A_7C15#;

   function Random (Bound : Positive) return Natural is
   begin
      Random_State := Random_State xor Shift_Left (Random_State, 13);
      Random_State := Random_State xor Shift_Right (Random_State, 7);
      Random_State := Random_State xor Shift_Left (Random_State, 17);
      return Natural (Random_State mod Unsigned_64 (Bound));
   end Random;

   --  A random key: mostly small integers (the array part), some large ones, integral floats
   --  (which are the same keys as integers), other floats, booleans and object handles.
   function Random_Key return Value is
   begin
      case Random (10) is
         when 0 .. 3 => return Integer_Value_Of (Integer_64 (Random (80) + 1));
         when 4      => return Integer_Value_Of (Integer_64 (Random (1_000_000)) - 500_000);
         when 5      =>
            return Float_Value_Of (Pyro.Floats.From_Integer (Integer_64 (Random (80) + 1)));
         when 6      =>
            return Float_Value_Of
                     (Pyro.Floats.Arithmetic
                        (Pyro.Floats.Divide, Pyro.Floats.From_Integer (Integer_64 (Random (1000))),
                         Pyro.Floats.From_Integer (7)));
         when 7      => return Boolean_Value_Of (Random (2) = 0);
         when others => return Object_Value_Of (Valid_Handle (Random (300) + 1));
      end case;
   end Random_Key;

   --  The table against the reference map, through long random sequences of operations.
   procedure Test_Tables_Model is
      T         : Table;
      Budget    : Memory_Budget := Create (Default_Limit);
      Reference : Reference_Maps.Map;
      Key, K    : Value;
      Item      : Value;
      Status    : Set_Status;
      Success   : Boolean;
      Same      : Boolean := True;
   begin
      Set_Seed (T, (K0 => 16#0123#, K1 => 16#4567#));
      for Step in 1 .. 200_000 loop
         Key := Random_Key;
         K := Key_Of (Key);
         case Random (10) is
            when 0 .. 4 =>
               Item := Integer_Value_Of (Integer_64 (Step));
               Set (T, Budget, Key, Item, Status);
               Same := Same and then Status = Done;
               Reference.Include (K, Item);
            when 5 .. 6 =>
               Set (T, Budget, Key, Nil, Status);
               Same := Same and then Status = Done;
               Reference.Exclude (K);
            when 7 =>
               Resize (T, Budget, Random (100), Random (100) + Natural (Reference.Length), Success);
            when others =>
               null;
         end case;
         Item := Get (T, Key);
         if Reference.Contains (K) then
            Same := Same and then Item = Reference.Element (K);
         else
            Same := Same and then Item = Nil;
         end if;
         if not Same then
            Put_Line ("tables: model differs at step" & Integer'Image (Step));
            exit;
         end if;
      end loop;
      Check (Same, "tables: random operations agree with the reference map");
      --  Every key, by traversal, deleting every other key on the way.
      declare
         Seen      : Reference_Maps.Map;
         Next_Key  : Value;
         Next_Item : Value;
         Visit     : Next_Status;
         Current   : Value := Nil;
         Toggle    : Boolean := False;
         Agreed    : Boolean := True;
      begin
         loop
            Next (T, Current, Next_Key, Next_Item, Visit);
            exit when Visit /= Found;
            Agreed := Agreed and then not Seen.Contains (Next_Key)
              and then Reference.Contains (Next_Key)
              and then Reference.Element (Next_Key) = Next_Item;
            Seen.Include (Next_Key, Next_Item);
            Toggle := not Toggle;
            if Toggle then
               Set (T, Budget, Next_Key, Nil, Status);
               Reference.Exclude (Next_Key);
            end if;
            Current := Next_Key;
         end loop;
         Check (Visit = Finished, "tables: traversal ends");
         Check (Agreed, "tables: traversal gives each key once, with its value");
         Check (Natural (Seen.Length) >= Natural (Reference.Length),
                "tables: traversal while deleting misses no key");
      end;
      Check (Get (T, Nil) = Nil, "tables: nil key reads nil");
      Set (T, Budget, Nil, Integer_Value_Of (1), Status);
      Check (Status = Invalid_Key, "tables: nil key cannot be set");
      Clear (T, Budget);
      Check (Used (Budget) = 0, "tables: Clear releases everything");
   end Test_Tables_Model;

   --  The length of sequences, and a border when there are holes.
   procedure Test_Tables_Length is
      T      : Table;
      Budget : Memory_Budget := Create (Default_Limit);
      Status : Set_Status;
      N      : Integer_64;
   begin
      Check (Length (T) = 0, "length: empty table");
      for Index in 1 .. 1000 loop
         Set (T, Budget, Integer_Value_Of (Integer_64 (Index)), Boolean_Value_Of (True), Status);
         if Index mod 97 = 0 then
            Check (Length (T) = Integer_64 (Index), "length: sequence of" & Index'Image);
         end if;
      end loop;
      Set (T, Budget, Integer_Value_Of (500), Nil, Status);
      N := Length (T);
      Check ((N = 0 or else Get (T, Integer_Value_Of (N)) /= Nil)
             and then Get (T, Integer_Value_Of (N + 1)) = Nil, "length: a border with a hole");
      Clear (T, Budget);
   end Test_Tables_Length;

   --  Long churn of inserts and deletes: probe sequences stay short.
   procedure Test_Tables_Probes is
      T       : Table;
      Budget  : Memory_Budget := Create (Default_Limit);
      Status  : Set_Status;
      Longest : Natural := 0;
   begin
      Set_Seed (T, (K0 => 16#DEAD_BEEF#, K1 => 16#CAFE#));
      for Round in 0 .. 49 loop
         for Index in 1 .. 2_000 loop
            --  Keys spaced by a large power of two, the worst case for a hash taken modulo
            --  a power of two without mixing; and object handles in sequence.
            Set (T, Budget, Integer_Value_Of (Integer_64 (Round * 2_000 + Index) * 2 ** 20),
                 Boolean_Value_Of (True), Status);
            Set (T, Budget, Object_Value_Of (Valid_Handle (Round * 2_000 + Index)),
                 Boolean_Value_Of (True), Status);
         end loop;
         for Index in 1 .. 1_500 loop
            Set (T, Budget, Integer_Value_Of (Integer_64 (Round * 2_000 + Index) * 2 ** 20), Nil,
                 Status);
         end loop;
         Longest := Natural'Max (Longest, Longest_Probe (T));
      end loop;
      Put_Line ("tables: longest probe after churn:" & Longest'Image);
      Check (Longest <= 64, "tables: probe sequences stay short under churn");
      Clear (T, Budget);
   end Test_Tables_Probes;

   --  The objects reachable from Roots, found by a breadth-first walk over Child_At: what the
   --  collector must keep, computed without it.
   type Handle_Flags is array (Valid_Handle range <>) of Boolean;

   function Reachable (H : Heap; Roots : Pyro.Garbage_Collector.Root_Array) return Handle_Flags is
      Result : Handle_Flags (1 .. Slot_Count (H)) := [others => False];
      Queue  : array (1 .. Natural (Slot_Count (H))) of Valid_Handle;
      Head   : Natural := 0;
      Tail   : Natural := 0;

      procedure Reach (Item : Value) is
      begin
         if Item.Kind = Object_Value and then not Result (Item.Object) then
            Result (Item.Object) := True;
            Tail := Tail + 1;
            Queue (Tail) := Item.Object;
         end if;
      end Reach;
   begin
      for Root of Roots loop
         Reach (Root);
      end loop;
      while Head < Tail loop
         Head := Head + 1;
         for Position in 1 .. Child_Count (H, Queue (Head)) loop
            Reach (Child_At (H, Queue (Head), Position));
         end loop;
      end loop;
      return Result;
   end Reachable;

   --  Random graphs of strings and tables, random roots: the collector frees exactly what
   --  cannot be reached, the tables it keeps still hold what they held, and freeing returns
   --  the memory, so the same round of allocations ends at the same budget.
   procedure Test_Collector_Random is
      Budget   : Memory_Budget := Create (Default_Limit);
      After    : array (1 .. 2) of Byte_Count := [others => 0];
      Kept     : Natural := 0;
      Freed    : Natural := 0;
   begin
      for Round in 1 .. 40 loop
         declare
            H        : Heap;
            Objects  : array (1 .. 300) of Object_Handle := [others => No_Object];
            Status   : Set_Status;
            Complete : Boolean;
            Count    : constant Positive := 20 + Random (280);
            Roots    : Pyro.Garbage_Collector.Root_Array (1 .. Random (6));
            Before   : Handle_Flags (1 .. 300);
            Keys     : array (1 .. 300) of Value := [others => Nil];
            Items    : array (1 .. 300) of Value := [others => Nil];
            Holder   : array (1 .. 300) of Object_Handle := [others => No_Object];
            Stored   : Natural := 0;
         begin
            for Index in 1 .. Count loop
               if Random (3) = 0 then
                  New_String (H, Budget, Bytes ("s" & Natural'Image (Random (100))),
                              Objects (Index));
               else
                  New_Table (H, Budget, Objects (Index));
               end if;
            end loop;
            --  Random edges, sometimes removed again (a removed key stays referred to by its
            --  dead node until the table is rehashed, which the walk over Child_At sees).
            for Edge in 1 .. Count * 2 loop
               declare
                  From : constant Object_Handle := Objects (Random (Count) + 1);
                  To   : constant Object_Handle := Objects (Random (Count) + 1);
                  Key  : constant Value :=
                    (if Random (2) = 0 then Integer_Value_Of (Integer_64 (Random (20) + 1))
                     else Object_Value_Of (Objects (Random (Count) + 1)));
               begin
                  if Kind_Of (H, From) = Table_Object then
                     Table_Set (H, Budget, From, Key,
                                (if Random (8) = 0 then Nil else Object_Value_Of (To)), Status);
                     Check (Status = Done, "collector: edge stored");
                  end if;
               end;
            end loop;
            --  What each table holds now, to read back after collecting.
            for Index in 1 .. Count loop
               if Kind_Of (H, Objects (Index)) = Table_Object and then Stored < Keys'Last then
                  Stored := Stored + 1;
                  Holder (Stored) := Objects (Index);
                  Keys (Stored) := Integer_Value_Of (Integer_64 (Random (20) + 1));
                  Items (Stored) := Table_Get (H, Objects (Index), Keys (Stored));
               end if;
            end loop;
            for R in Roots'Range loop
               Roots (R) := Object_Value_Of (Objects (Random (Count) + 1));
            end loop;
            declare
               Expected : constant Handle_Flags := Reachable (H, Roots);
            begin
               for Handle in Before'Range loop
                  Before (Handle) := Handle <= Slot_Count (H)
                                     and then Kind_Of (H, Handle) /= Free_Object;
               end loop;
               Pyro.Garbage_Collector.Collect (H, Budget, Roots, Complete);
               Check (Complete, "collector: marking completes");
               for Handle in Expected'Range loop
                  Check (Expected (Handle) = (Kind_Of (H, Handle) /= Free_Object),
                         "collector: kept exactly the reachable objects");
                  if Before (Handle) then
                     if Expected (Handle) then
                        Kept := Kept + 1;
                     else
                        Freed := Freed + 1;
                     end if;
                  end if;
               end loop;
               for Index in 1 .. Stored loop
                  if Expected (Holder (Index)) then
                     Check (Table_Get (H, Holder (Index), Keys (Index)) = Items (Index),
                            "collector: kept tables hold what they held");
                  end if;
               end loop;
            end;
            --  Collecting again with every survivor as a root frees nothing.
            declare
               Survivors : Pyro.Garbage_Collector.Root_Array (1 .. Natural (Slot_Count (H)));
               Used_Now  : constant Byte_Count := Used (Budget);
            begin
               for Handle in 1 .. Slot_Count (H) loop
                  Survivors (Positive (Handle)) :=
                    (if Kind_Of (H, Handle) = Free_Object then Nil else Object_Value_Of (Handle));
               end loop;
               Pyro.Garbage_Collector.Collect (H, Budget, Survivors, Complete);
               for Handle in 1 .. Slot_Count (H) loop
                  Check ((Kind_Of (H, Handle) = Free_Object)
                         = (Survivors (Positive (Handle)) = Nil),
                         "collector: roots keep everything");
               end loop;
               Check (Used (Budget) = Used_Now, "collector: nothing to free, nothing released");
            end;
            Clear (H, Budget);
            Check (Used (Budget) = 0, "collector: Clear releases everything");
         end;
      end loop;
      Check (Kept > 0 and then Freed > 0, "collector: rounds kept and freed objects");

      --  The same allocations twice, then everything freed: the budget ends where it did.
      for Pass in After'Range loop
         declare
            H        : Heap;
            Item     : Object_Handle;
            Previous : Object_Handle := No_Object;
            Status   : Set_Status;
            Complete : Boolean;
            None     : Pyro.Garbage_Collector.Root_Array (1 .. 0);
         begin
            for Round in 1 .. 2 loop
               for Index in 1 .. 500 loop
                  New_Table (H, Budget, Item);
                  if Previous /= No_Object then
                     Table_Set (H, Budget, Item, Integer_Value_Of (1), Object_Value_Of (Previous),
                                Status);
                  end if;
                  Previous := Item;
                  New_String (H, Budget, Bytes ("text" & Natural'Image (Index)), Item);
               end loop;
               Previous := No_Object;
               Pyro.Garbage_Collector.Collect (H, Budget, None, Complete);
            end loop;
            After (Pass) := Used (Budget);
            for Handle in 1 .. Slot_Count (H) loop
               Check (Kind_Of (H, Handle) = Free_Object, "collector: no roots frees everything");
            end loop;
            Clear (H, Budget);
         end;
      end loop;
      Check (After (1) = After (2) and then Used (Budget) = 0,
             "collector: freed memory returns to the budget");
   end Test_Collector_Random;

   --  Strings freed by the collector leave the intern set: making the same bytes again gives
   --  a string, interned again.
   procedure Test_Collector_Interning is
      H        : Heap;
      Budget   : Memory_Budget := Create (Default_Limit);
      A, B, C  : Object_Handle;
      Complete : Boolean;
      None     : Pyro.Garbage_Collector.Root_Array (1 .. 0);
   begin
      New_String (H, Budget, Bytes ("weak"), A);
      New_String (H, Budget, Bytes ("kept"), B);
      Pyro.Garbage_Collector.Collect (H, Budget, [1 => Object_Value_Of (B)], Complete);
      Check (Kind_Of (H, A) = Free_Object and then Kind_Of (H, B) = String_Object,
             "collector: unreachable string freed, root kept");
      New_String (H, Budget, Bytes ("kept"), C);
      Check (C = B, "collector: kept string still interned");
      New_String (H, Budget, Bytes ("weak"), A);
      New_String (H, Budget, Bytes ("weak"), C);
      Check (A /= No_Object and then C = A and then String_Length (H, A) = 4,
             "collector: freed string made and interned again");
      Pyro.Garbage_Collector.Collect (H, Budget, None, Complete);
      Clear (H, Budget);
      Check (Used (Budget) = 0, "collector: interning Clear releases everything");
   end Test_Collector_Interning;

   --  Closures, upvalues and host functions: their references keep objects alive, their
   --  numbers are kept, and freeing them returns their memory.
   procedure Test_Collector_Objects is
      H        : Heap;
      Budget   : Memory_Budget := Create (Default_Limit);
      Closure  : Object_Handle;
      Cell     : Object_Handle;
      Host     : Object_Handle;
      Inner    : Object_Handle;
      Meta     : Object_Handle;
      Complete : Boolean;
      None     : Pyro.Garbage_Collector.Root_Array (1 .. 0);
   begin
      New_Object (H, Budget, Closure_Object, 7, 2, Closure);
      New_Object (H, Budget, Upvalue_Object, 3, 1, Cell);
      New_Object (H, Budget, Host_Function_Object, 42, 0, Host);
      New_Table (H, Budget, Inner);
      New_Table (H, Budget, Meta);
      Check (Closure /= No_Object and then Cell /= No_Object and then Host /= No_Object
             and then Inner /= No_Object and then Meta /= No_Object, "objects: allocated");
      Check (Kind_Of (H, Closure) = Closure_Object and then Tag_Of (H, Closure) = 7
             and then Reference_Count (H, Closure) = 2
             and then Reference_At (H, Closure, 1) = Nil
             and then Kind_Of (H, Host) = Host_Function_Object and then Tag_Of (H, Host) = 42
             and then Reference_Count (H, Inner) = 1 and then Reference_At (H, Inner, 1) = Nil,
             "objects: kinds, numbers and references");
      --  closure -> upvalue -> table -> metatable
      Set_Reference (H, Closure, 2, Object_Value_Of (Cell));
      Set_Reference (H, Cell, 1, Object_Value_Of (Inner));
      Set_Reference (H, Inner, 1, Object_Value_Of (Meta));
      Set_Tag (H, Cell, 0);
      Check (Tag_Of (H, Cell) = 0 and then Reference_At (H, Closure, 2) = Object_Value_Of (Cell),
             "objects: references and numbers set");
      Pyro.Garbage_Collector.Collect (H, Budget, [1 => Object_Value_Of (Closure)], Complete);
      Check (Complete and then Kind_Of (H, Closure) = Closure_Object
             and then Kind_Of (H, Cell) = Upvalue_Object
             and then Kind_Of (H, Inner) = Table_Object
             and then Kind_Of (H, Meta) = Table_Object
             and then Kind_Of (H, Host) = Free_Object,
             "objects: references keep objects, the rest is freed");
      Pyro.Garbage_Collector.Collect (H, Budget, None, Complete);
      Check (Kind_Of (H, Closure) = Free_Object and then Kind_Of (H, Meta) = Free_Object,
             "objects: no roots frees everything");
      Clear (H, Budget);
      Check (Used (Budget) = 0, "objects: Clear releases everything");
   end Test_Collector_Objects;

   --  Large graphs within the limit: a chain of tables deeper than any stack, and one table
   --  with many children. Marking uses the gray list, so depth costs no recursion.
   procedure Test_Collector_Stress is
      H        : Heap;
      Budget   : Memory_Budget := Create (Default_Limit);
      First    : Object_Handle;
      Item     : Object_Handle;
      Previous : Object_Handle;
      Wide     : Object_Handle;
      Status   : Set_Status;
      Complete : Boolean;
      Live     : Natural := 0;
   begin
      New_Table (H, Budget, First);
      Previous := First;
      for Index in 1 .. 100_000 loop
         New_Table (H, Budget, Item);
         Table_Set (H, Budget, Previous, Integer_Value_Of (1), Object_Value_Of (Item), Status);
         Previous := Item;
      end loop;
      New_Table (H, Budget, Wide);
      for Index in 1 .. 50_000 loop
         New_Table (H, Budget, Item);
         Table_Set (H, Budget, Wide, Integer_Value_Of (Integer_64 (Index)), Object_Value_Of (Item),
                    Status);
      end loop;
      Check (Status = Done, "collector: stress graph built");
      Pyro.Garbage_Collector.Collect (H, Budget, [Object_Value_Of (First), Object_Value_Of (Wide)],
                              Complete);
      for Handle in 1 .. Slot_Count (H) loop
         if Kind_Of (H, Handle) /= Free_Object then
            Live := Live + 1;
         end if;
      end loop;
      Check (Complete and then Live = 150_002, "collector: deep and wide graphs kept");
      Pyro.Garbage_Collector.Collect (H, Budget, [1 => Object_Value_Of (Wide)], Complete);
      Live := 0;
      for Handle in 1 .. Slot_Count (H) loop
         if Kind_Of (H, Handle) /= Free_Object then
            Live := Live + 1;
         end if;
      end loop;
      Check (Complete and then Live = 50_001, "collector: dropped chain freed");
      Clear (H, Budget);
      Check (Used (Budget) = 0, "collector: stress Clear releases everything");
   end Test_Collector_Stress;

begin
   Test_Number_Images;
   Test_Tables_Model;
   Test_Tables_Length;
   Test_Tables_Probes;
   Test_Heap_Strings;
   Test_Heap_Many;
   Test_Hash;
   Test_Interning;
   Test_Collector_Random;
   Test_Collector_Interning;
   Test_Collector_Stress;
   Test_Collector_Objects;
   if Failures > 0 then
      Put_Line (Natural'Image (Failures) & " failure(s)");
      Ada.Command_Line.Set_Exit_Status (1);
   end if;
end Runtime_Test;
