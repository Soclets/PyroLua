--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  The dispatch loop's step: decodes the running frame's instruction and runs its handler.

private package Pyro.Virtual_Machine.Execution with SPARK_Mode => On, Always_Terminates is

   --  Executes the instruction of the running frame.
   procedure Step (M : in out Machine; Budget : in out Memory_Budget)
   with
     Global => null,
     Pre    => Is_Valid (M) and then Running (M),
     Post   => Is_Valid (M) and then Is_Loaded (M) and then Limit (Budget) = Limit (Budget)'Old;

end Pyro.Virtual_Machine.Execution;
