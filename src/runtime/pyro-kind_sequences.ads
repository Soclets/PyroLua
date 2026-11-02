--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  [proof] Sequences of object kinds, indexed by handle: the ghost view of what every heap
--  slot holds, through which tables and the collector state that handles refer to objects.

pragma SPARK_Mode (On);

with SPARK.Containers.Functional.Vectors;
with Pyro.Values;

package Pyro.Kind_Sequences is new SPARK.Containers.Functional.Vectors
  (Index_Type           => Pyro.Values.Valid_Handle,
   Element_Type         => Pyro.Values.Object_Kind,
   "="                  => Pyro.Values."=",
   Use_Logical_Equality => True);
