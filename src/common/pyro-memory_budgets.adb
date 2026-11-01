--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  The memory budget: every growth of Pyro's memory is charged here first, against a limit.

package body Pyro.Memory_Budgets with SPARK_Mode => On is

   procedure Charge (Budget : in out Memory_Budget; Bytes : Byte_Count; Success : out Boolean) is
   begin
      Success := Bytes <= Budget.Limit - Budget.Used;
      if Success then
         Budget.Used := Budget.Used + Bytes;
      end if;
   end Charge;

   procedure Release (Budget : in out Memory_Budget; Bytes : Byte_Count) is
   begin
      if Bytes <= Budget.Used then
         Budget.Used := Budget.Used - Bytes;
      else
         Budget.Used := 0;
      end if;
   end Release;

end Pyro.Memory_Budgets;
