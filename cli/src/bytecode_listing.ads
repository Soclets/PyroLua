--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  Listings of compiled chunks for the pyrolua program.

--  [trusted] Console output, outside the proven library.
pragma SPARK_Mode (Off);

with Pyro.Bytecode;
with Pyro.Sources;
with Pyro.Symbols;

package Bytecode_Listing is

   --  [puc luac.c:PrintFunction] Writes every prototype of Item to standard output, the main
   --  function first and each function's nested ones after it, as luac -l -l does. With
   --  Lua_Style the format is luac's, prototypes named by made-up addresses; otherwise opcodes
   --  have Pyro's names and prototypes are named by their number.
   procedure Print
     (Item      : Pyro.Bytecode.Chunk;
      Symbols   : Pyro.Symbols.Symbol_Table;
      Source    : Pyro.Sources.Source;
      Lua_Style : Boolean);

end Bytecode_Listing;
