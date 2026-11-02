--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  [proof] Sequences of value sequences, indexed by handle: the ghost view of what every
--  heap object holds, the graph the collector walks.

pragma SPARK_Mode (On);

with SPARK.Containers.Functional.Vectors;
with Pyro.Value_Sequences;
with Pyro.Values;

package Pyro.Graph_Sequences is new SPARK.Containers.Functional.Vectors
  (Index_Type           => Pyro.Values.Valid_Handle,
   Element_Type         => Pyro.Value_Sequences.Sequence,
   "="                  => Pyro.Value_Sequences."=",
   Use_Logical_Equality => True,
   Eq_Logical_Eq        => Pyro.Value_Sequences.Lemma_Eq_Extensional);
