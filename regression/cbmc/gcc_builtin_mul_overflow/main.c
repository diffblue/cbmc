#include <assert.h>
#include <limits.h>
#include <stdint.h>

#ifndef __GNUC__
_Bool __builtin_mul_overflow();
_Bool __builtin_mul_overflow_p();
_Bool __builtin_smul_overflow(int, int, int *);
_Bool __builtin_smull_overflow(long, long, long *);
_Bool __builtin_smulll_overflow(long long, long long, long long *);
_Bool __builtin_umul_overflow(unsigned int, unsigned int, unsigned int *);
_Bool __builtin_umull_overflow(unsigned long, unsigned long, unsigned long *);
_Bool __builtin_umulll_overflow(
  unsigned long long,
  unsigned long long,
  unsigned long long *);
#endif

#define A_VALUE_X_SO_THAT_X_TIMES_X_DOES_NOT_OVERFLOW(T)                       \
  (((T)(1)) << (sizeof(T) * CHAR_BIT) / 2 - 1)

void check_int(void)
{
  int result;
  assert(!__builtin_smul_overflow(1, 1, &result));
  assert(result == 1);
  int const lt_isqrt_of_int_max =
    A_VALUE_X_SO_THAT_X_TIMES_X_DOES_NOT_OVERFLOW(int);
  assert(!__builtin_smul_overflow(
    lt_isqrt_of_int_max, lt_isqrt_of_int_max, &result));
  assert(result == lt_isqrt_of_int_max * lt_isqrt_of_int_max);
  assert(__builtin_smul_overflow(
    lt_isqrt_of_int_max << 1, lt_isqrt_of_int_max << 1, &result));
  assert(0 && "reachability");
}

void check_long(void)
{
  long result;
  assert(!__builtin_smull_overflow(1l, 1l, &result));
  assert(result == 1l);
  long const lt_isqrt_of_long_max =
    A_VALUE_X_SO_THAT_X_TIMES_X_DOES_NOT_OVERFLOW(long);
  assert(!__builtin_smull_overflow(
    lt_isqrt_of_long_max, lt_isqrt_of_long_max, &result));
  assert(result == lt_isqrt_of_long_max * lt_isqrt_of_long_max);
  assert(__builtin_smull_overflow(
    lt_isqrt_of_long_max << 1, lt_isqrt_of_long_max << 1, &result));
  assert(0 && "reachability");
}

void check_long_long(void)
{
  long long result;
  assert(!__builtin_smulll_overflow(1ll, 1ll, &result));
  assert(result == 1ll);
  long long const lt_isqrt_of_long_long_max =
    A_VALUE_X_SO_THAT_X_TIMES_X_DOES_NOT_OVERFLOW(long long);
  assert(!__builtin_smulll_overflow(
    lt_isqrt_of_long_long_max, lt_isqrt_of_long_long_max, &result));
  assert(result == lt_isqrt_of_long_long_max * lt_isqrt_of_long_long_max);
  assert(__builtin_smulll_overflow(
    lt_isqrt_of_long_long_max << 1, lt_isqrt_of_long_long_max << 1, &result));
  assert(0 && "reachability");
}

void check_unsigned(void)
{
  unsigned result;
  assert(!__builtin_umul_overflow(1u, 1u, &result));
  assert(result == 1u);
  unsigned const lt_isqrt_of_unsigned_max =
    A_VALUE_X_SO_THAT_X_TIMES_X_DOES_NOT_OVERFLOW(unsigned);
  assert(!__builtin_umul_overflow(
    lt_isqrt_of_unsigned_max, lt_isqrt_of_unsigned_max, &result));
  assert(result == lt_isqrt_of_unsigned_max * lt_isqrt_of_unsigned_max);
  assert(__builtin_umul_overflow(
    lt_isqrt_of_unsigned_max << 1, lt_isqrt_of_unsigned_max << 1, &result));
  assert(0 && "reachability");
}

void check_unsigned_long(void)
{
  unsigned long result;
  assert(!__builtin_umull_overflow(1ul, 1ul, &result));
  assert(result == 1ul);
  unsigned long const lt_isqrt_of_unsigned_long_max =
    A_VALUE_X_SO_THAT_X_TIMES_X_DOES_NOT_OVERFLOW(unsigned long);
  assert(!__builtin_umull_overflow(
    lt_isqrt_of_unsigned_long_max, lt_isqrt_of_unsigned_long_max, &result));
  assert(
    result == lt_isqrt_of_unsigned_long_max * lt_isqrt_of_unsigned_long_max);
  assert(__builtin_umull_overflow(
    lt_isqrt_of_unsigned_long_max << 1,
    lt_isqrt_of_unsigned_long_max << 1,
    &result));
  assert(0 && "reachability");
}

void check_unsigned_long_long(void)
{
  unsigned long long result;
  assert(!__builtin_umulll_overflow(1ull, 1ull, &result));
  assert(result == 1ull);
  unsigned long long const lt_isqrt_of_unsigned_long_long_max =
    A_VALUE_X_SO_THAT_X_TIMES_X_DOES_NOT_OVERFLOW(unsigned long long);
  assert(!__builtin_umulll_overflow(
    lt_isqrt_of_unsigned_long_long_max,
    lt_isqrt_of_unsigned_long_long_max,
    &result));
  assert(
    result ==
    lt_isqrt_of_unsigned_long_long_max * lt_isqrt_of_unsigned_long_long_max);
  assert(__builtin_umulll_overflow(
    lt_isqrt_of_unsigned_long_long_max << 1,
    lt_isqrt_of_unsigned_long_long_max << 1,
    &result));
  assert(0 && "reachability");
}

void check_generic(void)
{
  unsigned char small_result;
  long long big_result;

  assert(__builtin_mul_overflow(100, 100, &small_result));
  assert(!__builtin_mul_overflow(100, 100, &big_result));
  assert(big_result == 10000);
  assert(!__builtin_mul_overflow(10, 10, &small_result));
  assert(small_result == 100);
  assert(!__builtin_mul_overflow(INT_MAX, INT_MAX, &big_result));
  assert(big_result == 4611686014132420609ll);
  assert(__builtin_mul_overflow(INT_MAX * 2ll, INT_MAX * 2ll, &big_result));
  assert(0 && "reachability");
}

int main(void)
{
  check_int();
  check_long();
  check_long_long();
  check_unsigned();
  check_unsigned_long();
  check_unsigned_long_long();
  check_generic();
  return 0;
}
