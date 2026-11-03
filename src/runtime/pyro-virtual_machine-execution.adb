--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  The dispatch loop's step: decodes the running frame's instruction and runs its handler.

with Pyro.Floats;
with Pyro.Virtual_Machine.Arithmetic;
with Pyro.Virtual_Machine.Comparisons;
with Pyro.Virtual_Machine.Indexing;
with Pyro.Virtual_Machine.Loops;

package body Pyro.Virtual_Machine.Execution with SPARK_Mode => On is

   use Pyro.Bytecode;

   procedure Step (M : in out Machine; Budget : in out Memory_Budget) is
      I : constant Instruction := Current (M);
      V : constant Frame_View := View (M) with Ghost;
      A : constant Natural range 0 .. 255 := Natural (I.A);
      B : constant Natural range 0 .. 255 := Natural (I.B);
      C : constant Natural range 0 .. 255 := Natural (I.C);
   begin
      Lemma_View (M);
      Lemma_Fits (M);
      case I.Operation is
         when Move =>
            Set_Register (M, A, Register (M, B));
            Next (M);
         when Load_Integer =>
            Set_Register (M, A, Integer_Value_Of (Integer_64 (I.Wide) - Offset_sBx));
            Next (M);
         when Load_Float =>
            Set_Register
              (M, A,
               Float_Value_Of (Pyro.Floats.From_Integer (Integer_64 (I.Wide) - Offset_sBx)));
            Next (M);
         when Load_Constant =>
            Set_Register (M, A, Constant_At (M, Natural (I.Wide)));
            Next (M);
         when Load_Constant_Extra =>
            --  [puc lvm.c:OP_LOADKX] The constant's number is the next instruction's Ax.
            if Extra_Argument (M) < View (M).Constants then
               Set_Register (M, A, Constant_At (M, Extra_Argument (M)));
               Next (M, 1);
            else
               Raise_Runtime_Error (M, Budget, "internal error: bad constant");
            end if;
         when Concatenate =>
            Concatenate (M, Budget, A, B);
         when Close =>
            Close_From (M, A);
         when Load_False =>
            Set_Register (M, A, Boolean_Value_Of (False));
            Next (M);
         when Load_False_Skip =>
            Set_Register (M, A, Boolean_Value_Of (False));
            Next (M, 1);
         when Load_True =>
            Set_Register (M, A, Boolean_Value_Of (True));
            Next (M);
         when Load_Nil =>
            for Number in A .. A + B loop
               Set_Register (M, Number, Nil);
               pragma Loop_Invariant (Is_Valid (M) and then Running (M) and then View (M) = V);
            end loop;
            Next (M);
         when Get_Upvalue =>
            Set_Register (M, A, Upvalue (M, B));
            Next (M);
         when Set_Upvalue =>
            Set_Upvalue (M, B, Register (M, A));
            Next (M);
         when Pyro.Virtual_Machine.Indexing.Indexing_Instruction =>
            Pyro.Virtual_Machine.Indexing.Execute (M, Budget, I);
         when Add_Integer .. Shift_Right =>
            Pyro.Virtual_Machine.Arithmetic.Execute_Binary (M, Budget, I);
         when Metamethod_Binary .. Metamethod_Binary_Constant =>
            Pyro.Virtual_Machine.Arithmetic.Execute_Metamethod (M, Budget, I);
         when Negate .. Logical_Not =>
            Pyro.Virtual_Machine.Arithmetic.Execute_Unary (M, Budget, I);
         when Test_Opcode =>
            Pyro.Virtual_Machine.Comparisons.Execute (M, Budget, I);
         when For_Loop .. Generic_For_Loop =>
            Pyro.Virtual_Machine.Loops.Execute (M, Budget, I);
         when Jump =>
            Next (M, Integer (I.Wide) - Offset_sJ);
         when Closure =>
            Make_Closure (M, Budget, Natural (I.Wide), A);
         when Call =>
            Call_Register (M, Budget, A, (if B = 0 then -1 else B - 1), C - 1);
         when Tail_Call =>
            Tail_Call_Register (M, Budget, A, (if B = 0 then -1 else B - 1));
         when Return_Values =>
            Return_Registers (M, A, (if B = 0 then -1 else B - 1), I.K);
         when Return_None =>
            Return_Registers (M, 0, 0, False);
         when Return_One =>
            Return_Registers (M, A, 1, False);
         when Vararg_Prepare =>
            Prepare_Varargs (M, Budget, A);
         when Vararg =>
            Copy_Varargs (M, Budget, A, C - 1);
         when others =>
            Raise_Runtime_Error (M, Budget, "instruction not supported yet");
      end case;
   end Step;

end Pyro.Virtual_Machine.Execution;
