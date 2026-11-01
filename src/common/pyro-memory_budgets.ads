--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  The memory budget: every growth of Pyro's memory is charged here first, against a limit.

package Pyro.Memory_Budgets with SPARK_Mode => On, Pure, Always_Terminates is

   --  A number of bytes.
   type Byte_Count is range 0 .. 2 ** 62;

   --  The largest limit a budget can have.
   Maximum_Limit : constant Byte_Count := 2 ** 48;

   --  Memory limit used by the pyro executable when none is given: 1 GiB.
   Default_Limit : constant Byte_Count := 2 ** 30;

   --  How many bytes may be in use (the limit) and how many are (charged, not yet released).
   type Memory_Budget is private
   with Default_Initial_Condition => Limit (Memory_Budget) = 0 and then Used (Memory_Budget) = 0;

   --  The limit of Budget.
   function Limit (Budget : Memory_Budget) return Byte_Count
   with Global => null, Post => Limit'Result <= Maximum_Limit;

   --  The bytes currently charged to Budget. Never more than its limit.
   function Used (Budget : Memory_Budget) return Byte_Count
   with Global => null, Post => Used'Result <= Limit (Budget);

   --  A budget with nothing used and the given limit.
   function Create (Limit : Byte_Count) return Memory_Budget
   with
     Global => null,
     Pre    => Limit <= Maximum_Limit,
     Post   => Memory_Budgets.Limit (Create'Result) = Limit and then Used (Create'Result) = 0;

   --  Charges Bytes to Budget if that keeps it within its limit; otherwise leaves it unchanged
   --  and reports failure, which callers turn into a "not enough memory" error.
   procedure Charge (Budget : in out Memory_Budget; Bytes : Byte_Count; Success : out Boolean)
   with
     Global         => null,
     Contract_Cases =>
       (Bytes <= Limit (Budget) - Used (Budget) =>
          Success
          and then Used (Budget) = Used (Budget'Old) + Bytes
          and then Limit (Budget) = Limit (Budget'Old),
        others                                   =>
          not Success
          and then Used (Budget) = Used (Budget'Old)
          and then Limit (Budget) = Limit (Budget'Old));

   --  Gives back Bytes charged earlier. Releasing more than is used empties the budget rather
   --  than failing, since owners of memory cannot prove what other owners charged.
   procedure Release (Budget : in out Memory_Budget; Bytes : Byte_Count)
   with
     Global => null,
     Post   =>
       Limit (Budget) = Limit (Budget'Old)
       and then Used (Budget)
                = (if Bytes <= Used (Budget'Old) then Used (Budget'Old) - Bytes else 0);

private

   type Memory_Budget is record
      Limit : Byte_Count := 0;
      Used  : Byte_Count := 0;
   end record
   with Predicate => Limit <= Maximum_Limit and then Used <= Limit;

   function Limit (Budget : Memory_Budget) return Byte_Count is (Budget.Limit);

   function Used (Budget : Memory_Budget) return Byte_Count is (Budget.Used);

   function Create (Limit : Byte_Count) return Memory_Budget is ((Limit => Limit, Used => 0));

end Pyro.Memory_Budgets;
