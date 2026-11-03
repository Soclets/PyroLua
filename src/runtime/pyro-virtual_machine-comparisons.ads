--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  The handlers of the comparison and test instructions.

private package Pyro.Virtual_Machine.Comparisons with SPARK_Mode => On, Always_Terminates is

   --  [puc lvm.c:OP_EQ .. OP_TESTSET] Comparison or test instruction I, the running frame's:
   --  when its condition is not the one its k flag asks for, the jump after it is skipped;
   --  otherwise the jump runs next.
   procedure Execute
     (M : in out Machine; Budget : in out Memory_Budget; I : Pyro.Bytecode.Instruction)
   with
     Global => null,
     Pre    =>
       Is_Valid (M)
       and then Running (M)
       and then I = Current (M)
       and then I.Operation in Pyro.Bytecode.Test_Opcode
       and then Fits (View (M), I),
     Post   => Is_Valid (M) and then Is_Loaded (M) and then Limit (Budget) = Limit (Budget)'Old;

end Pyro.Virtual_Machine.Comparisons;
