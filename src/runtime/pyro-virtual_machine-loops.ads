--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  The handlers of the numeric and generic for loops.

private package Pyro.Virtual_Machine.Loops with SPARK_Mode => On, Always_Terminates is

   --  [puc lvm.c:OP_FORLOOP .. OP_TFORLOOP] Executes loop instruction I, the running frame's.
   procedure Execute
     (M : in out Machine; Budget : in out Memory_Budget; I : Pyro.Bytecode.Instruction)
   with
     Global => null,
     Pre    =>
       Is_Valid (M)
       and then Running (M)
       and then I = Current (M)
       and then I.Operation in Pyro.Bytecode.For_Loop .. Pyro.Bytecode.Generic_For_Loop
       and then Fits (View (M), I),
     Post   => Is_Valid (M) and then Is_Loaded (M) and then Limit (Budget) = Limit (Budget)'Old;

end Pyro.Virtual_Machine.Loops;
