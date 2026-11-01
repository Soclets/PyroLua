--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  Root of Pyro: limits and configuration constants shared by every stage.

package Pyro with SPARK_Mode => On, Pure is

   --  The largest chunk Pyro accepts, in bytes.
   Maximum_Source_Length : constant := 2 ** 28;

end Pyro;
