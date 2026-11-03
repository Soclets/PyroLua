--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  The host functions of the pyrolua program: the small fixed set test scripts use.

--  [trusted] Ordinary Ada around the machine's host-function protocol (docs/PROOFS.md, cli/).
pragma SPARK_Mode (Off);

with Pyro.Memory_Budgets;
with Pyro.Virtual_Machine;

package Host_Functions is

   --  Makes every host function a global of M. Success is False when Budget cannot pay.
   procedure Register_All
     (M       : in out Pyro.Virtual_Machine.Machine;
      Budget  : in out Pyro.Memory_Budgets.Memory_Budget;
      Success : out Boolean);

   --  Answers the host function M is waiting for.
   procedure Answer
     (M      : in out Pyro.Virtual_Machine.Machine;
      Budget : in out Pyro.Memory_Budgets.Memory_Budget);

   --  Writes what print buffered to the standard output.
   procedure Flush;

end Host_Functions;
