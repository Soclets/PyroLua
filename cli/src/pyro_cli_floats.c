/* SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
 *
 * Float formatting for the pyrolua program's listings.
 *
 * [trusted] luac prints float constants with LUA_NUMBER_FMT ("%.14g"); this does the same with
 * the C library, as luac does.
 */

#include <stdint.h>
#include <stdio.h>
#include <string.h>

/* Writes the float with bits 'bits' as "%.14g" into 'buffer' (NUL-terminated) and returns the
   length written. */
int pyro_format_float (uint64_t bits, char *buffer, int size) {
  double value;
  int length;
  memcpy(&value, &bits, sizeof value);
  length = snprintf(buffer, (size_t) size, "%.14g", value);
  return (length < 0) ? 0 : (length >= size ? size - 1 : length);
}
