--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  [proof] Sequences of values: the ghost view of every value a table holds, through which
--  the heap and the collector state which handles a table refers to.

pragma SPARK_Mode (On);

with SPARK.Containers.Functional.Vectors;
with Pyro.Values;

package Pyro.Value_Sequences is new SPARK.Containers.Functional.Vectors
  (Index_Type           => Positive,
   Element_Type         => Pyro.Values.Value,
   "="                  => Pyro.Values."=",
   Use_Logical_Equality => True);
