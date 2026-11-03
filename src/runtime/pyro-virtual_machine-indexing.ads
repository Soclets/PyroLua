--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  The handlers of the table instructions: indexing, new tables, lists and lengths.

private package Pyro.Virtual_Machine.Indexing with SPARK_Mode => On, Always_Terminates is

   --  The instructions these handlers execute.
   subtype Indexing_Instruction is Pyro.Bytecode.Opcode
     with Static_Predicate =>
       Indexing_Instruction in Pyro.Bytecode.Get_Table_Upvalue .. Pyro.Bytecode.Self
                             | Pyro.Bytecode.Set_List | Pyro.Bytecode.Length;

   --  [puc lvm.c:luaV_execute] Executes instruction I, the running frame's.
   procedure Execute
     (M : in out Machine; Budget : in out Memory_Budget; I : Pyro.Bytecode.Instruction)
   with
     Global => null,
     Pre    =>
       Is_Valid (M)
       and then Running (M)
       and then I = Current (M)
       and then I.Operation in Indexing_Instruction
       and then Fits (View (M), I),
     Post   => Is_Valid (M) and then Is_Loaded (M) and then Limit (Budget) = Limit (Budget)'Old;

end Pyro.Virtual_Machine.Indexing;
