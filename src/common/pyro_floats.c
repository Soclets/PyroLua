/* SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
 *
 * Decimal-to-float conversion for the trusted body of Pyro.Floats.
 *
 * [trusted] strtod_l with an explicit "C" locale, so that a host calling setlocale (for
 * example with ',' as the decimal separator) cannot change how Lua numerals are read. This is
 * the same correctly rounded conversion luac uses, minus its locale dependence.
 */

#if defined(__linux__)
#define _GNU_SOURCE
#endif

#include <locale.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#if defined(__APPLE__)
#include <xlocale.h>
#endif

/* Converts the NUL-terminated decimal numeral 'text'. Returns 1 and stores the IEEE 754 bits of
   the result in 'bits' when strtod consumed the whole text, 0 otherwise. */
int pyro_decimal_to_bits (const char *text, uint64_t *bits) {
  locale_t c_locale = newlocale(LC_NUMERIC_MASK, "C", (locale_t) 0);
  char *end;
  double value;
  if (c_locale == (locale_t) 0)
    return 0;
  value = strtod_l(text, &end, c_locale);
  freelocale(c_locale);
  if (end == text || *end != '\0')
    return 0;
  memcpy(bits, &value, sizeof value);
  return 1;
}
