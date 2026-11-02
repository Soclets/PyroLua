--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  [proof] Sequences of handles: paths through the heap, by which the collector states what
--  is reachable.

pragma SPARK_Mode (On);

with SPARK.Containers.Functional.Vectors;
with Pyro.Values;

package Pyro.Handle_Sequences is new SPARK.Containers.Functional.Vectors
  (Index_Type           => Positive,
   Element_Type         => Pyro.Values.Valid_Handle,
   "="                  => Pyro.Values."=",
   Use_Logical_Equality => True);
