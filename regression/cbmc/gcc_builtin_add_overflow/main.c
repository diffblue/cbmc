#include <assert.h>
#include <limits.h>

#ifndef __GNUC__
_Bool __builtin_add_overflow();
_Bool __builtin_add_overflow_p();
_Bool __builtin_sadd_overflow(int, int, int *);
_Bool __builtin_saddl_overflow(long, long, long *);
_Bool __builtin_saddll_overflow(long long, long long, long long *);
_Bool __builtin_uadd_overflow(unsigned int, unsigned int, unsigned int *);
_Bool __builtin_uaddl_overflow(unsigned long, unsigned long, unsigned long *);
_Bool __builtin_uaddll_overflow(
  unsigned long long,
  unsigned long long,
  unsigned long long *);
#endif

void check_int(void)
{
  int const one = 1;
  int result;

  assert(!__builtin_sadd_overflow(one, one, &result));
  assert(result == 2);
  assert(__builtin_sadd_overflow(one, INT_MAX, &result));
  assert(!__builtin_sadd_overflow(INT_MAX / 2, INT_MAX / 2, &result));
  assert(result + 1 == INT_MAX);
  assert(__builtin_sadd_overflow(INT_MAX / 2 + 2, INT_MAX / 2 + 2, &result));
  assert(__builtin_sadd_overflow(-one, INT_MIN, &result));
  assert(0 && "reachability");
}

void check_long(void)
{
  long const one = 1l;
  long result;

  assert(!__builtin_saddl_overflow(one, one, &result));
  assert(result == 2l);
  assert(__builtin_saddl_overflow(one, LONG_MAX, &result));
  assert(!__builtin_saddl_overflow(LONG_MAX / 2l, LONG_MAX / 2l, &result));
  assert(result + 1l == LONG_MAX);
  assert(
    __builtin_saddl_overflow(LONG_MAX / 2l + 2l, LONG_MAX / 2l + 2l, &result));
  assert(__builtin_saddl_overflow(-one, LONG_MIN, &result));
  assert(0 && "reachability");
}

void check_long_long(void)
{
  long long const one = 1ll;
  long long result;

  assert(!__builtin_saddll_overflow(one, one, &result));
  assert(result == 2ll);
  assert(__builtin_saddll_overflow(one, LLONG_MAX, &result));
  assert(!__builtin_saddll_overflow(LLONG_MAX / 2ll, LLONG_MAX / 2ll, &result));
  assert(result + 1ll == LLONG_MAX);
  assert(__builtin_saddll_overflow(
    LLONG_MAX / 2ll + 2ll, LLONG_MAX / 2ll + 2ll, &result));
  assert(__builtin_saddll_overflow(-one, LLONG_MIN, &result));
  assert(0 && "reachability");
}

void check_unsigned(void)
{
  unsigned const one = 1u;
  unsigned result;

  assert(!__builtin_uadd_overflow(one, one, &result));
  assert(result == 2u);
  assert(!__builtin_uadd_overflow(UINT_MAX / 2, UINT_MAX / 2, &result));
  assert(result + 1u == UINT_MAX);
  assert(__builtin_uadd_overflow(UINT_MAX / 2 + 2, UINT_MAX / 2 + 2, &result));
  assert(__builtin_uadd_overflow(one, UINT_MAX, &result));
  assert(0 && "reachability");
}

void check_unsigned_long(void)
{
  unsigned long const one = 1ul;
  unsigned long result;

  assert(!__builtin_uaddl_overflow(one, one, &result));
  assert(result == 2ul);
  assert(!__builtin_uaddl_overflow(ULONG_MAX / 2, ULONG_MAX / 2, &result));
  assert(result + 1ul == ULONG_MAX);
  assert(
    __builtin_uaddl_overflow(ULONG_MAX / 2 + 2, ULONG_MAX / 2 + 2, &result));
  assert(__builtin_uaddl_overflow(one, ULONG_MAX, &result));
  assert(0 && "reachability");
}

void check_unsigned_long_long(void)
{
  unsigned long long const one = 1ull;
  unsigned long long result;

  assert(!__builtin_uaddll_overflow(one, one, &result));
  assert(result == 2ull);
  assert(!__builtin_uaddll_overflow(ULLONG_MAX / 2, ULLONG_MAX / 2, &result));
  assert(result + 1ull == ULLONG_MAX);
  assert(
    __builtin_uaddll_overflow(ULLONG_MAX / 2 + 2, ULLONG_MAX / 2 + 2, &result));
  assert(__builtin_uaddll_overflow(one, ULLONG_MAX, &result));
  assert(0 && "reachability");
}

void check_generic(void)
{
  unsigned char small_result;
  signed long long big_result;
  assert(!__builtin_add_overflow(17, 25, &small_result));
  assert(small_result == 42);
  assert(!__builtin_add_overflow(17, 25, &big_result));
  assert(big_result == 42ll);
  assert(__builtin_add_overflow(216, 129, &small_result));
  assert(!__builtin_add_overflow(216, 129, &big_result));
  assert(big_result == 345);
  assert(!__builtin_add_overflow(INT_MAX, INT_MAX, &big_result));
  assert(big_result == 2ll * INT_MAX);
  assert(
    __builtin_add_overflow(LLONG_MAX / 2 + 1, LLONG_MAX / 2 + 1, &big_result));
  assert(0 && "reachability");
}

void check_generic_p(void)
{
  unsigned char small_result = 0;
  signed long long big_result = 0;
  assert(!__builtin_add_overflow_p(17, 25, small_result));
  assert(small_result == 0);
  assert(!__builtin_add_overflow_p(17, 25, big_result));
  assert(big_result == 0);
  assert(0 && "reachability");
}

void check_non_const()
{
  int a, b, c, d, r;
  // this may overflow (negated assertion fails)
  assert(!__builtin_add_overflow(a, b, &r));
  // but need not overflow (assertion fails)
  assert(__builtin_add_overflow(c, d, &c));
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
  check_generic_p();
  check_non_const();
}
