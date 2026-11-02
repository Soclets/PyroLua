--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  [proof] Sequences of colours, indexed by handle: the ghost view of the collector's marks.

pragma SPARK_Mode (On);

with SPARK.Containers.Functional.Vectors;
with Pyro.Values;

package Pyro.Color_Sequences is new SPARK.Containers.Functional.Vectors
  (Index_Type           => Pyro.Values.Valid_Handle,
   Element_Type         => Pyro.Values.Object_Color,
   "="                  => Pyro.Values."=",
   Use_Logical_Equality => True);
