--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  Root of Pyro: limits and configuration constants shared by every stage.

package Pyro with SPARK_Mode => On, Pure is

   --  The largest chunk Pyro accepts, in bytes.
   Maximum_Source_Length : constant := 2 ** 28;

   --  A position in a byte array held by Pyro (a source, a lexer buffer, symbol text). Large
   --  enough for every byte array the front end builds from a source of maximum length.
   type Byte_Position is range 1 .. 2 ** 30;

end Pyro;
