#include <assert.h>
#include <limits.h>

#ifndef __GNUC__
int __builtin_ffs(int);
int __builtin_ffsl(long);
int __builtin_ffsll(long long);
#endif

#ifdef _MSC_VER
#  define _Static_assert(x, m) static_assert(x, m)
#endif

int __VERIFIER_nondet_int();

// http://graphics.stanford.edu/~seander/bithacks.html#ZerosOnRightMultLookup
static const int multiply_de_bruijn_bit_position[32] = {
  0,  1,  28, 2,  29, 14, 24, 3, 30, 22, 20, 15, 25, 17, 4,  8,
  31, 27, 13, 23, 21, 19, 16, 7, 26, 12, 18, 6,  11, 5,  10, 9};

int main()
{
  _Static_assert(__builtin_ffs(0) == 0, "");
  _Static_assert(__builtin_ffs(-1) == 1, "");
  _Static_assert(__builtin_ffs(INT_MIN) == sizeof(int) * 8, "");
  _Static_assert(__builtin_ffsl(INT_MIN) == sizeof(int) * 8, "");
  _Static_assert(__builtin_ffsl(LONG_MIN) == sizeof(long) * 8, "");
  _Static_assert(__builtin_ffsll(INT_MIN) == sizeof(int) * 8, "");
  _Static_assert(__builtin_ffsll(LLONG_MIN) == sizeof(long long) * 8, "");
  _Static_assert(__builtin_ffs(INT_MAX) == 1, "");

  int i = __VERIFIER_nondet_int();
  __CPROVER_assume(i != 0);
  __CPROVER_assume(sizeof(i) == 4);
  __CPROVER_assume(i > INT_MIN);
  assert(
    multiply_de_bruijn_bit_position
        [((unsigned)((i & -i) * 0x077CB531U)) >> 27] +
      1 ==
    __builtin_ffs(i));

  return 0;
}
