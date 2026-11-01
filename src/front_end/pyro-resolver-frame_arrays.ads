--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  Growable arrays of Frame for the resolver's walk.

pragma SPARK_Mode (On);

with Pyro.Growable_Arrays;

private package Pyro.Resolver.Frame_Arrays is new Pyro.Growable_Arrays
  (Index => Entry_Position, Element_Type => Frame, Default_Element => (others => <>),
   Element_Bytes => 12);
