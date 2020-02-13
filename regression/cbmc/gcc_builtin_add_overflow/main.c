#include <assert.h>
#include <limits.h>

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

  assert(!__builtin_uaddl_overflow(one, one, &result));
  assert(result == 2ull);
  assert(!__builtin_uaddll_overflow(ULLONG_MAX / 2, ULLONG_MAX / 2, &result));
  assert(result + 1ull == ULLONG_MAX);
  assert(
    __builtin_uaddll_overflow(ULLONG_MAX / 2 + 2, ULLONG_MAX / 2 + 2, &result));
  assert(__builtin_uaddl_overflow(one, ULLONG_MAX, &result));
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
}
