--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  Growable lists of diagnostics, as the parser and resolver report them.

pragma SPARK_Mode (On);

with Pyro.Diagnostics;
with Pyro.Growable_Arrays;

package Pyro.Diagnostic_Lists is new Pyro.Growable_Arrays
  (Index => Pyro.Diagnostics.Diagnostic_Position, Element_Type => Pyro.Diagnostics.Diagnostic,
   Default_Element => (others => <>), Element_Bytes => 192);
