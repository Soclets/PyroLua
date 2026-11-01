--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  Recursive-descent parser for Lua 5.4, building the syntax tree of a chunk.

with Pyro.Diagnostic_Lists;
with Pyro.Memory_Budgets; use Pyro.Memory_Budgets;
with Pyro.Sources;        use Pyro.Sources;
with Pyro.Symbols;        use Pyro.Symbols;
with Pyro.Syntax_Trees;   use Pyro.Syntax_Trees;

package Pyro.Parser with SPARK_Mode => On, Always_Terminates is

   --  [puc lparser.c:luaY_parser] Parses Source into Tree. Root is the main function's
   --  Function_Body (vararg, no parameters), or No_Node if memory ran out first.
   --
   --  Errors go to Problems, in the order they are found. After a syntax error inside
   --  ( ), [ ] or { } whose closing bracket is intact, parsing skips to that bracket and goes
   --  on; after any other syntax error, and after a lexical error, it stops, keeping the
   --  partial tree (blocks and functions cut short are marked Is_Incomplete). Errors PUC Lua
   --  finds while parsing that are not grammar errors ('...' outside a vararg function, an
   --  unknown attribute, two <close> variables in one list) are reported without stopping.
   procedure Parse
     (Source   : Sources.Source;
      Symbols  : in out Symbol_Table;
      Budget   : in out Memory_Budget;
      Tree     : in out Syntax_Tree;
      Problems : in out Diagnostic_Lists.Growable_Array;
      Root     : out Node_Index)
   with
     Global => null,
     Pre    => Is_Valid (Symbols) and then Is_Well_Formed (Tree),
     Post   =>
       Is_Valid (Symbols)
       and then Is_Well_Formed (Tree)
       and then Root <= Node_Count (Tree)
       and then Limit (Budget) = Limit (Budget)'Old;

end Pyro.Parser;
