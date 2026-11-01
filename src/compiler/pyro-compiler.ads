--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  The compiler: turns a chunk's syntax tree into the prototypes PUC Lua's luac would produce.

with Pyro.Bytecode;       use Pyro.Bytecode;
with Pyro.Diagnostic_Lists;
with Pyro.Memory_Budgets; use Pyro.Memory_Budgets;
with Pyro.Sources;        use Pyro.Sources;
with Pyro.Symbols;        use Pyro.Symbols;
with Pyro.Syntax_Trees;   use Pyro.Syntax_Trees;

package Pyro.Compiler with SPARK_Mode => On, Always_Terminates is

   --  [puc lparser.c, lcode.c] Compiles the chunk whose tree Parse built from Source (Root its
   --  main Function_Body), after the resolver, with Problems holding their errors. The
   --  prototypes are added to Result, which must be empty; the main function is the last one.
   --  When PUC Lua would stop at a compile-time limit (registers, local variables, upvalues,
   --  jump lengths), or when the compiler's output fails Is_Valid (an internal error), Result
   --  stays empty and the error is appended to Problems. A chunk with errors is compiled as
   --  far as PUC Lua would have compiled it before stopping at them, for its limit errors
   --  only (each with its detection point), and Result stays empty.
   procedure Compile
     (Source   : Sources.Source;
      Tree     : Syntax_Tree;
      Root     : Node_Index;
      Symbols  : in out Symbol_Table;
      Budget   : in out Memory_Budget;
      Problems : in out Diagnostic_Lists.Growable_Array;
      Result   : in out Chunk)
   with
     Global => null,
     Pre    =>
       Is_Well_Formed (Tree)
       and then Root <= Node_Count (Tree)
       and then Is_Valid (Symbols)
       and then Prototype_Count (Result) = 0,
     Post   =>
       Is_Valid (Symbols)
       and then Is_Well_Formed (Result)
       and then (Prototype_Count (Result) = 0 or else Is_Valid (Result))
       and then Limit (Budget) = Limit (Budget)'Old;

end Pyro.Compiler;
