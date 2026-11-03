--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  The handlers of the arithmetic, bitwise and logical instructions.

with Pyro.Floats;
with Pyro.Integer_Arithmetic;

package body Pyro.Virtual_Machine.Arithmetic with SPARK_Mode => On is

   use Pyro.Bytecode;

   --  [puc ltm.h:TMS] The binary operations, in the order of their metamethod events
   --  (First_Binary_Event is TM_ADD).
   type Binary_Operation is
     (Add_Operation, Subtract_Operation, Multiply_Operation, Modulo_Operation,
      Power_Operation, Divide_Operation, Floor_Divide_Operation, And_Operation,
      Or_Operation, Exclusive_Or_Operation, Shift_Left_Operation, Shift_Right_Operation);

   subtype Bitwise_Operation is Binary_Operation range And_Operation .. Shift_Right_Operation;

   --  The operation of metamethod event Event.
   function Event_Operation (Event : Byte) return Binary_Operation
   is (if Event in First_Binary_Event .. Last_Binary_Event
       then Binary_Operation'Val (Natural (Event) - Natural (First_Binary_Event))
       else Add_Operation);

   --  The operation of arithmetic instruction Code.
   function Operation_Of (Code : Opcode) return Binary_Operation
   is (case Code is
         when Add_Integer | Add_Constant | Add                        => Add_Operation,
         when Subtract_Constant | Subtract                            => Subtract_Operation,
         when Multiply_Constant | Multiply                            => Multiply_Operation,
         when Modulo_Constant | Modulo                                => Modulo_Operation,
         when Power_Constant | Power                                  => Power_Operation,
         when Divide_Constant | Divide                                => Divide_Operation,
         when Floor_Divide_Constant | Floor_Divide                    => Floor_Divide_Operation,
         when Bitwise_And_Constant | Bitwise_And                      => And_Operation,
         when Bitwise_Or_Constant | Bitwise_Or                        => Or_Operation,
         when Bitwise_Exclusive_Or_Constant | Bitwise_Exclusive_Or    => Exclusive_Or_Operation,
         when Shift_Left_Integer | Shift_Left                         => Shift_Left_Operation,
         when Shift_Right_Integer | Shift_Right                       => Shift_Right_Operation,
         when others                                                  => Add_Operation);

   --  The float operation of arithmetic operation Operation.
   function Float_Operation (Operation : Binary_Operation) return Pyro.Floats.Operation
   is (case Operation is
         when Add_Operation          => Pyro.Floats.Add,
         when Subtract_Operation     => Pyro.Floats.Subtract,
         when Multiply_Operation     => Pyro.Floats.Multiply,
         when Modulo_Operation       => Pyro.Floats.Modulo,
         when Power_Operation        => Pyro.Floats.Power,
         when Divide_Operation       => Pyro.Floats.Divide,
         when Floor_Divide_Operation => Pyro.Floats.Floor_Divide,
         when others                 => Pyro.Floats.Add);

   --  How an operation ended.
   type Outcome is
     (Computed,        --  Result holds the result
      Not_Numbers,     --  an operand is not a number: the metamethod instruction follows
      Not_Integers,    --  bitwise, an operand is a float with no integer value: likewise
      Modulo_By_Zero,  --  integer % 0
      Divide_By_Zero); --  integer // 0

   function Is_Number (Item : Value) return Boolean
   is (Item.Kind in Integer_Value | Float_Value);

   --  [puc lvm.c:luaV_tonumber_] Number Item as a float.
   function To_Float (Item : Value) return Pyro.Floats.Float_Bits
   is (if Item.Kind = Integer_Value then Pyro.Floats.From_Integer (Integer_Of (Item))
       else Item.Bits);

   --  [puc lvm.c:luaV_tointegerns] Item as an integer: an integer, or a float with an integral
   --  value (mode F2Ieq). Success is False otherwise.
   procedure To_Integer (Item : Value; Result : out Integer_64; Success : out Boolean)
   with Global => null
   is
   begin
      Result := 0;
      Success := False;
      if Item.Kind = Integer_Value then
         Result := Integer_Of (Item);
         Success := True;
      elsif Item.Kind = Float_Value then
         Pyro.Floats.To_Integer (Item.Bits, Result, Success);
      end if;
   end To_Integer;

   --  [puc lvm.c:op_arith, op_bitwise] Left Operation Right, without metamethods.
   procedure Compute
     (Operation : Binary_Operation;
      Left      : Value;
      Right     : Value;
      Result    : out Value;
      Status    : out Outcome)
   with
     Global => null,
     Post   =>
       (if Status = Computed
        then Is_Canonical (Result) and then Result.Kind /= Object_Value)
   is
      package Integers renames Pyro.Integer_Arithmetic;
      X, Y   : Integer_64;
      X_Fits : Boolean;
      Y_Fits : Boolean;
   begin
      Result := Nil;
      Status := Computed;
      if Operation in Bitwise_Operation then
         To_Integer (Left, X, X_Fits);
         To_Integer (Right, Y, Y_Fits);
         if not (X_Fits and then Y_Fits) then
            Status :=
              (if Is_Number (Left) and then Is_Number (Right) then Not_Integers
               else Not_Numbers);
            return;
         end if;
         Result :=
           Integer_Value_Of
             (case Bitwise_Operation (Operation) is
                when And_Operation          => Integers.Bitwise_And (X, Y),
                when Or_Operation           => Integers.Bitwise_Or (X, Y),
                when Exclusive_Or_Operation => Integers.Bitwise_Exclusive_Or (X, Y),
                when Shift_Left_Operation   => Integers.Shift_Left (X, Y),
                when Shift_Right_Operation  => Integers.Shift_Left (X, Integers.Negate (Y)));
      elsif Left.Kind = Integer_Value
        and then Right.Kind = Integer_Value
        and then Operation not in Power_Operation | Divide_Operation
      then
         X := Integer_Of (Left);
         Y := Integer_Of (Right);
         case Operation is
            when Add_Operation =>
               Result := Integer_Value_Of (Integers.Add (X, Y));
            when Subtract_Operation =>
               Result := Integer_Value_Of (Integers.Subtract (X, Y));
            when Multiply_Operation =>
               Result := Integer_Value_Of (Integers.Multiply (X, Y));
            when Modulo_Operation =>
               if Y = 0 then
                  Status := Modulo_By_Zero;
                  return;
               end if;
               Result := Integer_Value_Of (Integers.Modulo (X, Y));
            when others =>
               if Y = 0 then
                  Status := Divide_By_Zero;
                  return;
               end if;
               Result := Integer_Value_Of (Integers.Floor_Divide (X, Y));
         end case;
      elsif Is_Number (Left) and then Is_Number (Right) then
         Result :=
           Float_Value_Of
             (Pyro.Floats.Arithmetic
                (Float_Operation (Operation), To_Float (Left), To_Float (Right)));
      else
         Status := Not_Numbers;
      end if;
   end Compute;

   --  [puc ltm.c:luaT_trybinTM] Operation on Left and Right has no metamethod: raises the
   --  error, naming the operand at fault.
   procedure Binary_Error
     (M         : in out Machine;
      Budget    : in out Memory_Budget;
      Operation : Binary_Operation;
      Left      : Value;
      Right     : Value)
   with
     Global => null,
     Pre    => Is_Valid (M) and then Is_Loaded (M),
     Post   => Is_Valid (M) and then Is_Loaded (M) and then Limit (Budget) = Limit (Budget)'Old
   is
   begin
      if Operation in Bitwise_Operation and then Is_Number (Left) and then Is_Number (Right)
      then
         --  [puc ldebug.c:luaG_tointerror]
         Raise_Runtime_Error (M, Budget, "number has no integer representation");
      elsif Operation in Bitwise_Operation then
         --  [puc ldebug.c:luaG_opinterror]
         Raise_Runtime_Error
           (M, Budget,
            "attempt to perform bitwise operation on a "
            & Type_Name (M, (if Is_Number (Left) then Right else Left)) & " value");
      else
         Raise_Runtime_Error
           (M, Budget,
            "attempt to perform arithmetic on a "
            & Type_Name (M, (if Is_Number (Left) then Right else Left)) & " value");
      end if;
   end Binary_Error;

   procedure Execute_Binary
     (M : in out Machine; Budget : in out Memory_Budget; I : Pyro.Bytecode.Instruction)
   is
      A      : constant Natural := Natural (I.A);
      B      : constant Natural := Natural (I.B);
      C      : constant Natural := Natural (I.C);
      Left   : Value;
      Right  : Value;
      Result : Value;
      Status : Outcome;
   begin
      Lemma_View (M);
      case I.Operation is
         when Add_Integer | Shift_Right_Integer =>
            Left := Register (M, B);
            Right := Integer_Value_Of (Integer_64 (C) - Offset_sC);
         when Shift_Left_Integer =>
            Left := Integer_Value_Of (Integer_64 (C) - Offset_sC);
            Right := Register (M, B);
         when Add_Constant .. Bitwise_Exclusive_Or_Constant =>
            Left := Register (M, B);
            Right := Constant_At (M, C);
         when others =>
            Left := Register (M, B);
            Right := Register (M, C);
      end case;
      Compute (Operation_Of (I.Operation), Left, Right, Result, Status);
      case Status is
         when Computed =>
            Set_Register (M, A, Result);
            Next (M, 1);
         when Not_Numbers | Not_Integers =>
            Next (M);
         when Modulo_By_Zero =>
            Raise_Runtime_Error (M, Budget, "attempt to perform 'n%0'");
         when Divide_By_Zero =>
            Raise_Runtime_Error (M, Budget, "attempt to divide by zero");
      end case;
   end Execute_Binary;

   procedure Execute_Metamethod
     (M : in out Machine; Budget : in out Memory_Budget; I : Pyro.Bytecode.Instruction)
   is
      Left  : Value;
      Right : Value;
   begin
      Lemma_View (M);
      Left := Register (M, Natural (I.A));
      case I.Operation is
         when Metamethod_Binary =>
            Right := Register (M, Natural (I.B));
         when Metamethod_Binary_Integer =>
            Right := Integer_Value_Of (Integer_64 (I.B) - Offset_sC);
         when others =>
            Right := Constant_At (M, Natural (I.B));
      end case;
      if I.K then
         Binary_Error (M, Budget, Event_Operation (I.C), Right, Left);
      else
         Binary_Error (M, Budget, Event_Operation (I.C), Left, Right);
      end if;
   end Execute_Metamethod;

   procedure Execute_Unary
     (M : in out Machine; Budget : in out Memory_Budget; I : Pyro.Bytecode.Instruction)
   is
      A       : constant Natural := Natural (I.A);
      Operand : Value;
      X       : Integer_64;
      Fits    : Boolean;
   begin
      Lemma_View (M);
      Operand := Register (M, Natural (I.B));
      case I.Operation is
         when Negate =>
            if Operand.Kind = Integer_Value then
               Set_Register
                 (M, A, Integer_Value_Of (Pyro.Integer_Arithmetic.Negate (Integer_Of (Operand))));
               Next (M);
            elsif Operand.Kind = Float_Value then
               Set_Register
                 (M, A,
                  Float_Value_Of (Pyro.Floats.Arithmetic (Pyro.Floats.Negate, Operand.Bits, 0)));
               Next (M);
            else
               Raise_Runtime_Error
                 (M, Budget, "attempt to perform arithmetic on a " & Type_Name (M, Operand)
                             & " value");
            end if;
         when Bitwise_Not =>
            To_Integer (Operand, X, Fits);
            if Fits then
               Set_Register (M, A, Integer_Value_Of (Pyro.Integer_Arithmetic.Bitwise_Not (X)));
               Next (M);
            elsif Is_Number (Operand) then
               Raise_Runtime_Error (M, Budget, "number has no integer representation");
            else
               Raise_Runtime_Error
                 (M, Budget, "attempt to perform bitwise operation on a "
                             & Type_Name (M, Operand) & " value");
            end if;
         when others =>
            Set_Register
              (M, A,
               Boolean_Value_Of
                 (Operand.Kind = Nil_Value or else Operand = Boolean_Value_Of (False)));
            Next (M);
      end case;
   end Execute_Unary;

end Pyro.Virtual_Machine.Arithmetic;
