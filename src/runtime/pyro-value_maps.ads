--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  [proof] Maps from values to values: the ghost model of a table's contents.

pragma SPARK_Mode (On);

with SPARK.Containers.Functional.Maps;
with Pyro.Values;

package Pyro.Value_Maps is new SPARK.Containers.Functional.Maps
  (Key_Type                       => Pyro.Values.Value,
   Element_Type                   => Pyro.Values.Value,
   Equivalent_Keys                => Pyro.Values."=",
   "="                            => Pyro.Values."=",
   Enable_Handling_Of_Equivalence => True);
