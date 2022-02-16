#include <assert.h>
#include <limits.h>

#ifndef __GNUC__
_Bool __builtin_sub_overflow();
_Bool __builtin_sub_overflow_p();
_Bool __builtin_ssub_overflow(int, int, int *);
_Bool __builtin_ssubl_overflow(long, long, long *);
_Bool __builtin_ssubll_overflow(long long, long long, long long *);
_Bool __builtin_usub_overflow(unsigned int, unsigned int, unsigned int *);
_Bool __builtin_usubl_overflow(unsigned long, unsigned long, unsigned long *);
_Bool __builtin_usubll_overflow(
  unsigned long long,
  unsigned long long,
  unsigned long long *);
#endif

void check_int(void)
{
  int result;
  assert(!__builtin_ssub_overflow(1, 1, &result));
  assert(result == 0);
  assert(__builtin_ssub_overflow(INT_MIN, 1, &result));
  assert(!__builtin_ssub_overflow(INT_MIN / 2, INT_MAX / 2, &result));
  assert(result - 1 == INT_MIN);
  assert(0 && "reachability");
}

void check_long(void)
{
  long result;
  assert(!__builtin_ssubl_overflow(1l, 1l, &result));
  assert(result == 0l);
  assert(__builtin_ssubl_overflow(LONG_MIN, 1l, &result));
  assert(!__builtin_ssubl_overflow(LONG_MIN / 2l, LONG_MAX / 2l, &result));
  assert(result - 1l == LONG_MIN);
  assert(0 && "reachability");
}

void check_long_long(void)
{
  long result;
  assert(!__builtin_ssubll_overflow(1ll, 1ll, &result));
  assert(result == 0ll);
  assert(__builtin_ssubll_overflow(LLONG_MIN, 1ll, &result));
  assert(!__builtin_ssubll_overflow(LLONG_MIN / 2ll, LLONG_MAX / 2ll, &result));
#if !defined(_WIN32)
  // Visual Studio x86/32 bit has an 8-byte "long long" type with corresponding
  // LLONG_MAX and LLONG_MIN constants (9223372036854775807i64 and
  // -9223372036854775807i64 - 1, respectively), but compiles these to 32-bit
  // values. The result is that -LLONG_MAX wraps around to the 32-bit value of
  // -LLONG_MIN (-2147483648), with the consequence that result == LLONG_MIN
  // after the above subtraction. Therefore, disable this assertion on Visual
  // Studio x86/32 bit.
  assert(result - 1ll == LLONG_MIN);
#endif
  assert(0 && "reachability");
}

void check_unsigned(void)
{
  unsigned result;
  assert(!__builtin_usub_overflow(1u, 1u, &result));
  assert(result == 0u);
  assert(__builtin_usub_overflow(0u, 1u, &result));
  assert(!__builtin_usub_overflow(UINT_MAX / 2u, UINT_MAX / 2u, &result));
  assert(result == 0u);
  assert(__builtin_usub_overflow(UINT_MAX / 2u, UINT_MAX, &result));
  assert(0 && "reachability");
}

void check_unsigned_long(void)
{
  unsigned long result;
  assert(!__builtin_usubl_overflow(1ul, 1ul, &result));
  assert(result == 0ul);
  assert(__builtin_usubl_overflow(0ul, 1ul, &result));
  assert(!__builtin_usubl_overflow(ULONG_MAX / 2ul, ULONG_MAX / 2ul, &result));
  assert(result == 0ul);
  assert(__builtin_usubl_overflow(ULONG_MAX / 2ul, ULONG_MAX, &result));
  assert(0 && "reachability");
}

void check_unsigned_long_long(void)
{
  unsigned long long result;
  assert(!__builtin_usubll_overflow(1ull, 1ull, &result));
  assert(result == 0ull);
  assert(__builtin_usubll_overflow(0ull, 1ull, &result));
  assert(
    !__builtin_usubll_overflow(ULLONG_MAX / 2ull, ULLONG_MAX / 2ull, &result));
  assert(result == 0ull);
  assert(__builtin_usubll_overflow(ULLONG_MAX / 2ull, ULLONG_MAX, &result));
  assert(0 && "reachability");
}

void check_generic(void)
{
  unsigned char small_result;
  long long big_result;

  assert(__builtin_sub_overflow(5, 10, &small_result));
  assert(!__builtin_sub_overflow(5, 10, &big_result));
  assert(big_result == -5ll);
  assert(!__builtin_sub_overflow(10, 5, &small_result));
  assert(small_result == 5);
  assert(!__builtin_sub_overflow(10, 5, &big_result));
  assert(big_result == 5ll);
  assert(!__builtin_sub_overflow(INT_MIN, INT_MAX, &big_result));
  assert(big_result == 2ll * INT_MIN + 1);
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
}
