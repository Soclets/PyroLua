--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  Growable arrays of Jump_Entry for the resolver's walk.

pragma SPARK_Mode (On);

with Pyro.Growable_Arrays;

private package Pyro.Resolver.Jump_Arrays is new Pyro.Growable_Arrays
  (Index => Entry_Position, Element_Type => Jump_Entry, Default_Element => (others => <>),
   Element_Bytes => 24);
