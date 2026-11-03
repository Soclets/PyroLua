/* SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
 *
 * Decimal-to-float conversion and float arithmetic for the trusted body of Pyro.Floats.
 *
 * [trusted] strtod_l with an explicit "C" locale, so that a host calling setlocale (for
 * example with ',' as the decimal separator) cannot change how Lua numerals are read. This is
 * the same correctly rounded conversion luac uses, minus its locale dependence.
 */

#if defined(__linux__)
#define _GNU_SOURCE
#endif

#include <locale.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
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

static double to_double (uint64_t bits) {
  double value;
  memcpy(&value, &bits, sizeof value);
  return value;
}

static uint64_t to_bits (double value) {
  uint64_t bits;
  memcpy(&bits, &value, sizeof bits);
  return bits;
}

/* [trusted] Lua's float arithmetic, as llimits.h defines it (luai_numadd ... luai_nummod) and
   lobject.c's numarith applies it. 'kind' is the position in Pyro.Floats.Operation. */
uint64_t pyro_float_arithmetic (int kind, uint64_t left_bits, uint64_t right_bits) {
  double a = to_double(left_bits), b = to_double(right_bits), m;
  switch (kind) {
    case 0: return to_bits(a + b);
    case 1: return to_bits(a - b);
    case 2: return to_bits(a * b);
    case 3: return to_bits(a / b);
    case 4: return to_bits((b == 2) ? a * a : pow(a, b));
    case 5: return to_bits(floor(a / b));
    case 6:
      m = fmod(a, b);
      if ((m > 0) ? b < 0 : (m < 0 && b > 0)) m += b;
      return to_bits(m);
    default: return to_bits(-a);
  }
}

/* The conversion C (and Lua's cast_num) makes from a 64-bit integer. */
uint64_t pyro_integer_to_float (int64_t value) {
  return to_bits((double) value);
}

/* [trusted] luaV_flttointeger with F2Ieq and lua_numbertointeger: 1 and the integer when the
   float has an integral value in range, 0 otherwise. */
int pyro_float_to_integer (uint64_t bits, int64_t *result) {
  double value = to_double(bits);
  double floor_value = floor(value);
  if (value != floor_value)
    return 0;
  if (floor_value >= (double) INT64_MIN && floor_value < -(double) INT64_MIN) {
    *result = (int64_t) floor_value;
    return 1;
  }
  return 0;
}

/* [trusted] Writes the float with bits 'bits' as LUA_NUMBER_FMT ("%.14g") into 'buffer'
   (NUL-terminated, at most 'size' bytes with the NUL) and returns the length written, as
   lobject.c's tostringbuff does with the C library. */
int pyro_format_float (uint64_t bits, char *buffer, int size) {
  int length = snprintf(buffer, (size_t) size, "%.14g", to_double(bits));
  return (length < 0) ? 0 : (length >= size ? size - 1 : length);
}
