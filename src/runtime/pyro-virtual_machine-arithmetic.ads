--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  The handlers of the arithmetic, bitwise and logical instructions.

private package Pyro.Virtual_Machine.Arithmetic with SPARK_Mode => On, Always_Terminates is

   --  [puc lvm.c:op_arith, op_bitwise] An arithmetic or bitwise instruction I, the running
   --  frame's: its result, or on to the metamethod instruction after it.
   procedure Execute_Binary
     (M : in out Machine; Budget : in out Memory_Budget; I : Pyro.Bytecode.Instruction)
   with
     Global => null,
     Pre    =>
       Is_Valid (M)
       and then Running (M)
       and then I = Current (M)
       and then I.Operation in Pyro.Bytecode.Add_Integer .. Pyro.Bytecode.Shift_Right
       and then Fits (View (M), I),
     Post   => Is_Valid (M) and then Is_Loaded (M) and then Limit (Budget) = Limit (Budget)'Old;

   --  [puc lvm.c:OP_MMBIN] The metamethod instruction I after an arithmetic one that failed.
   procedure Execute_Metamethod
     (M : in out Machine; Budget : in out Memory_Budget; I : Pyro.Bytecode.Instruction)
   with
     Global => null,
     Pre    =>
       Is_Valid (M)
       and then Running (M)
       and then I = Current (M)
       and then I.Operation
                in Pyro.Bytecode.Metamethod_Binary .. Pyro.Bytecode.Metamethod_Binary_Constant
       and then Fits (View (M), I),
     Post   => Is_Valid (M) and then Is_Loaded (M) and then Limit (Budget) = Limit (Budget)'Old;

   --  [puc lvm.c:OP_UNM, OP_BNOT, OP_NOT] Unary minus, bitwise not or not, instruction I.
   procedure Execute_Unary
     (M : in out Machine; Budget : in out Memory_Budget; I : Pyro.Bytecode.Instruction)
   with
     Global => null,
     Pre    =>
       Is_Valid (M)
       and then Running (M)
       and then I = Current (M)
       and then I.Operation in Pyro.Bytecode.Negate .. Pyro.Bytecode.Logical_Not
       and then Fits (View (M), I),
     Post   => Is_Valid (M) and then Is_Loaded (M) and then Limit (Budget) = Limit (Budget)'Old;

end Pyro.Virtual_Machine.Arithmetic;
