--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  The handlers of the numeric and generic for loops.

with Pyro.Floats;
with Pyro.Integer_Arithmetic;

package body Pyro.Virtual_Machine.Loops with SPARK_Mode => On is

   use Pyro.Bytecode;

   package Integers renames Pyro.Integer_Arithmetic;

   --  The float bits of 0.0.
   Zero : constant Pyro.Floats.Float_Bits := 0;

   function As_Float (Item : Value) return Pyro.Floats.Float_Bits
   is (if Item.Kind = Integer_Value then Pyro.Floats.From_Integer (Integer_Of (Item))
       else Item.Bits);

   function Positive_Float (F : Pyro.Floats.Float_Bits) return Boolean
   is (Pyro.Floats.Compare (Pyro.Floats.Less_Than, Zero, F));

   --  [puc lvm.c:luaV_tointeger] Number Item as an integer: itself, or a float rounded down
   --  (Up False) or up when that is in range. Success is False otherwise.
   procedure Round
     (Item : Value; Up : Boolean; Result : out Integer_64; Success : out Boolean)
   with Global => null
   is
      One     : constant Pyro.Floats.Float_Bits := Pyro.Floats.From_Integer (1);
      Rounded : Pyro.Floats.Float_Bits;
   begin
      Result := 0;
      Success := False;
      if Item.Kind = Integer_Value then
         Result := Integer_Of (Item);
         Success := True;
      elsif Item.Kind = Float_Value then
         if Up then
            Rounded :=
              Pyro.Floats.Arithmetic
                (Pyro.Floats.Negate,
                 Pyro.Floats.Arithmetic
                   (Pyro.Floats.Floor_Divide,
                    Pyro.Floats.Arithmetic (Pyro.Floats.Negate, Item.Bits, Zero), One),
                 Zero);
         else
            Rounded := Pyro.Floats.Arithmetic (Pyro.Floats.Floor_Divide, Item.Bits, One);
         end if;
         Pyro.Floats.To_Integer (Rounded, Result, Success);
      end if;
   end Round;

   --  [puc ldebug.c:luaG_forerror]
   procedure For_Error
     (M : in out Machine; Budget : in out Memory_Budget; What : String; Item : Value)
   with
     Global => null,
     Pre    => Is_Valid (M) and then Is_Loaded (M) and then What'Length <= 16,
     Post   => Is_Valid (M) and then Is_Loaded (M) and then Limit (Budget) = Limit (Budget)'Old
   is
   begin
      Raise_Runtime_Error
        (M, Budget,
         "bad 'for' " & What & " (number expected, got " & Type_Name (M, Item) & ")");
   end For_Error;

   --  [puc lvm.c:forprep] Prepares a numeric loop whose registers start at A: Skip is True
   --  when it runs no iteration. Raised is True when it raised an error.
   procedure Prepare
     (M      : in out Machine;
      Budget : in out Memory_Budget;
      A      : Natural;
      Skip   : out Boolean;
      Raised : out Boolean)
   with
     Global => null,
     Pre    =>
       Is_Valid (M) and then Running (M) and then A <= 255 and then A + 3 < View (M).Registers,
     Post   =>
       Is_Valid (M)
       and then Is_Loaded (M)
       and then Limit (Budget) = Limit (Budget)'Old
       and then (if not Raised then Running (M) and then View (M) = View (M)'Old)
   is
      Init  : constant Value := Register (M, A);
      Bound : constant Value := Register (M, A + 1);
      Step  : constant Value := Register (M, A + 2);
      Limit_Value : Value;
      Step_Value  : Value;
      Init_Value  : Value;
      Valid       : Boolean;
      Last        : Integer_64;
      Count       : Unsigned_64;
      I, S        : Integer_64;
   begin
      Skip := True;
      Raised := False;
      if Init.Kind = Integer_Value and then Step.Kind = Integer_Value then
         I := Integer_Of (Init);
         S := Integer_Of (Step);
         if S = 0 then
            Raised := True;
            Raise_Runtime_Error (M, Budget, "'for' step is zero");
            return;
         end if;
         Set_Register (M, A + 3, Init);
         --  [puc lvm.c:forlimit] The limit as an integer, rounded toward the loop's start.
         To_Number (M, Bound, Limit_Value, Valid);
         if not Valid then
            Raised := True;
            For_Error (M, Budget, "limit", Bound);
            return;
         end if;
         Round (Limit_Value, Up => S < 0, Result => Last, Success => Valid);
         if not Valid then
            --  A float out of the integers' range.
            if Positive_Float (Limit_Value.Bits) then
               if S < 0 then
                  return;
               end if;
               Last := Integer_64'Last;
            else
               if S > 0 then
                  return;
               end if;
               Last := Integer_64'First;
            end if;
         end if;
         if (if S > 0 then I > Last else I < Last) then
            return;
         end if;
         --  The number of iterations after the first, as an unsigned count.
         if S > 0 then
            Count := Integers.To_Unsigned (Last) - Integers.To_Unsigned (I);
            if S /= 1 then
               Count := Count / Integers.To_Unsigned (S);
            end if;
         else
            Count := Integers.To_Unsigned (I) - Integers.To_Unsigned (Last);
            Count := Count / (Integers.To_Unsigned (-(S + 1)) + 1);
         end if;
         Set_Register (M, A + 1, Integer_Value_Of (Integers.To_Signed (Count)));
         Skip := False;
      else
         To_Number (M, Bound, Limit_Value, Valid);
         if not Valid then
            Raised := True;
            For_Error (M, Budget, "limit", Bound);
            return;
         end if;
         To_Number (M, Step, Step_Value, Valid);
         if not Valid then
            Raised := True;
            For_Error (M, Budget, "step", Step);
            return;
         end if;
         To_Number (M, Init, Init_Value, Valid);
         if not Valid then
            Raised := True;
            For_Error (M, Budget, "initial value", Init);
            return;
         end if;
         if Pyro.Floats.Is_Zero (As_Float (Step_Value)) then
            Raised := True;
            Raise_Runtime_Error (M, Budget, "'for' step is zero");
            return;
         end if;
         if (if Positive_Float (As_Float (Step_Value))
             then Pyro.Floats.Compare
                    (Pyro.Floats.Less_Than, As_Float (Limit_Value), As_Float (Init_Value))
             else Pyro.Floats.Compare
                    (Pyro.Floats.Less_Than, As_Float (Init_Value), As_Float (Limit_Value)))
         then
            return;
         end if;
         Set_Register (M, A, Float_Value_Of (As_Float (Init_Value)));
         Set_Register (M, A + 1, Float_Value_Of (As_Float (Limit_Value)));
         Set_Register (M, A + 2, Float_Value_Of (As_Float (Step_Value)));
         Set_Register (M, A + 3, Float_Value_Of (As_Float (Init_Value)));
         Skip := False;
      end if;
   end Prepare;

   procedure Execute
     (M : in out Machine; Budget : in out Memory_Budget; I : Pyro.Bytecode.Instruction)
   is
      A    : constant Natural range 0 .. 255 := Natural (I.A);
      C    : constant Natural range 0 .. 255 := Natural (I.C);
      Jump : constant Integer := Integer (I.Wide);
   begin
      Lemma_View (M);
      case I.Operation is
         when For_Prepare =>
            declare
               Skip, Raised : Boolean;
            begin
               Prepare (M, Budget, A, Skip, Raised);
               if Raised then
                  return;
               elsif Skip then
                  Next (M, Jump + 1);
               else
                  Next (M);
               end if;
            end;

         when For_Loop =>
            declare
               Step  : constant Value := Register (M, A + 2);
               Index : constant Value := Register (M, A);
               Bound : constant Value := Register (M, A + 1);
               Count      : Unsigned_64 := 0;
               Next_Index : Value;
            begin
               if Step.Kind = Integer_Value then
                  if Bound.Kind = Integer_Value then
                     Count := Integers.To_Unsigned (Integer_Of (Bound));
                  end if;
                  if Bound.Kind = Integer_Value and then Index.Kind = Integer_Value
                    and then Count > 0
                  then
                     Next_Index :=
                       Integer_Value_Of (Integers.Add (Integer_Of (Index), Integer_Of (Step)));
                     Set_Register (M, A + 1, Integer_Value_Of (Integers.To_Signed (Count - 1)));
                     Set_Register (M, A, Next_Index);
                     Set_Register (M, A + 3, Next_Index);
                     Next (M, -Jump);
                  else
                     Next (M);
                  end if;
               elsif Step.Kind = Float_Value and then Index.Kind = Float_Value
                 and then Bound.Kind = Float_Value
               then
                  --  [puc lvm.c:floatforloop]
                  Next_Index :=
                    Float_Value_Of
                      (Pyro.Floats.Arithmetic (Pyro.Floats.Add, Index.Bits, Step.Bits));
                  if (if Positive_Float (Step.Bits)
                      then Pyro.Floats.Compare
                             (Pyro.Floats.Less_Equal, Next_Index.Bits, Bound.Bits)
                      else Pyro.Floats.Compare
                             (Pyro.Floats.Less_Equal, Bound.Bits, Next_Index.Bits))
                  then
                     Set_Register (M, A, Next_Index);
                     Set_Register (M, A + 3, Next_Index);
                     Next (M, -Jump);
                  else
                     Next (M);
                  end if;
               else
                  Next (M);
               end if;
            end;

         when Generic_For_Prepare =>
            --  [puc lvm.c:OP_TFORPREP] The closing value becomes a to-be-closed variable.
            Mark_To_Close (M, Budget, A + 3, Jump);

         when Generic_For_Call =>
            --  [puc lvm.c:OP_TFORCALL] The iterator, called with the state and the control,
            --  its results from register A + 4; TFORLOOP runs when it returns.
            Set_Register (M, A + 4, Register (M, A));
            Set_Register (M, A + 5, Register (M, A + 1));
            Set_Register (M, A + 6, Register (M, A + 2));
            Call_Register (M, Budget, A + 4, 2, C);

         when others =>
            declare
               Control : constant Value := Register (M, A + 4);
            begin
               if Control.Kind /= Nil_Value then
                  Set_Register (M, A + 2, Control);
                  Next (M, -Jump);
               else
                  Next (M);
               end if;
            end;
      end case;
   end Execute;

end Pyro.Virtual_Machine.Loops;
