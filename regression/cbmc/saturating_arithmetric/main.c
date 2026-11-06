#include <limits.h>
#include <stdint.h>

int main()
{
  // Boundary saturation cases.
  __CPROVER_assert(
    __CPROVER_saturating_minus(INT_MIN, 1) == INT_MIN,
    "subtracting from INT_MIN");
  __CPROVER_assert(
    __CPROVER_saturating_plus(LONG_MAX, 1l) == LONG_MAX, "adding to LONG_MAX");
  __CPROVER_assert(
    __CPROVER_saturating_minus(-1, INT_MIN) == INT_MAX, "no overflow");
  __CPROVER_assert(
    __CPROVER_saturating_plus(ULONG_MAX, 1ul) == ULONG_MAX,
    "adding to ULONG_MAX");
  __CPROVER_assert(
    __CPROVER_saturating_minus(10ul, ULONG_MAX) == 0, "subtracting ULONG_MAX");

  // Signed plus with negative overflow saturates to INT_MIN.
  __CPROVER_assert(
    __CPROVER_saturating_plus(INT_MIN, -1) == INT_MIN,
    "INT_MIN + (-1) saturates to INT_MIN");

  // Non-saturating sanity cases: the result is in range and must be exact.
  __CPROVER_assert(
    __CPROVER_saturating_plus(2, 3) == 5, "signed plus, no saturation");
  __CPROVER_assert(
    __CPROVER_saturating_minus(5, 3) == 2, "signed minus, no saturation");
  __CPROVER_assert(
    __CPROVER_saturating_plus(2u, 3u) == 5u, "unsigned plus, no saturation");
  __CPROVER_assert(
    __CPROVER_saturating_minus(5u, 3u) == 2u, "unsigned minus, no saturation");

  // 8-bit cases, exercising the width-1 / width bit extraction at a boundary
  // other than 32/64.
  __CPROVER_assert(
    __CPROVER_saturating_plus((int8_t)10, (int8_t)20) == (int8_t)30,
    "int8 plus, no saturation");
  __CPROVER_assert(
    __CPROVER_saturating_plus((int8_t)100, (int8_t)100) == (int8_t)127,
    "int8 plus saturates to INT8_MAX");
  __CPROVER_assert(
    __CPROVER_saturating_minus((int8_t)-100, (int8_t)100) == (int8_t)-128,
    "int8 minus saturates to INT8_MIN");
  __CPROVER_assert(
    __CPROVER_saturating_plus((uint8_t)200, (uint8_t)100) == (uint8_t)255,
    "uint8 plus saturates to UINT8_MAX");
  __CPROVER_assert(
    __CPROVER_saturating_minus((uint8_t)10, (uint8_t)20) == (uint8_t)0,
    "uint8 minus saturates to 0");

  return 0;
}
