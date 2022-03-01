#include <assert.h>
#include <limits.h>

#ifndef __GNUC__
int __builtin_ctz(unsigned int);
int __builtin_ctzl(unsigned long);
int __builtin_ctzll(unsigned long long);
#endif

#ifdef _MSC_VER
#  define _Static_assert(x, m) static_assert(x, m)
#endif

unsigned __VERIFIER_nondet_unsigned();

// http://graphics.stanford.edu/~seander/bithacks.html#ZerosOnRightMultLookup
static const int multiply_de_bruijn_bit_position[32] = {
  0,  1,  28, 2,  29, 14, 24, 3, 30, 22, 20, 15, 25, 17, 4,  8,
  31, 27, 13, 23, 21, 19, 16, 7, 26, 12, 18, 6,  11, 5,  10, 9};

int main()
{
  _Static_assert(__builtin_ctz(1) == 0, "");
  _Static_assert(__builtin_ctz(UINT_MAX) == 0, "");
  _Static_assert(
    __builtin_ctz(1U << (sizeof(unsigned) * 8 - 1)) == sizeof(unsigned) * 8 - 1,
    "");
  _Static_assert(
    __builtin_ctzl(1UL << (sizeof(unsigned) * 8 - 1)) ==
      sizeof(unsigned) * 8 - 1,
    "");
  _Static_assert(
    __builtin_ctzll(1ULL << (sizeof(unsigned) * 8 - 1)) ==
      sizeof(unsigned) * 8 - 1,
    "");

  unsigned u = __VERIFIER_nondet_unsigned();
  __CPROVER_assume(u != 0);
  __CPROVER_assume(sizeof(u) == 4);
  __CPROVER_assume(u > INT_MIN);
  assert(
    multiply_de_bruijn_bit_position
      [((unsigned)((u & -u) * 0x077CB531U)) >> 27] == __builtin_ctz(u));

  // a failing assertion should be generated as __builtin_ctz is undefined for 0
  int r = __builtin_ctz(0U);
  __CPROVER_assert(
    r == sizeof(unsigned) * 8, "count trailing zeros of 0 is bit width");

  return 0;
}
