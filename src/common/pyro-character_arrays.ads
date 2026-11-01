--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  Growable arrays of bytes, used for lexer buffers and symbol text.

pragma SPARK_Mode (On);

with Pyro.Growable_Arrays;

package Pyro.Character_Arrays is new Pyro.Growable_Arrays
  (Index => Pyro.Byte_Position, Element_Type => Character, Default_Element => ASCII.NUL,
   Element_Bytes => 1);
