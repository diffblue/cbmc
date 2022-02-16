#include <limits.h>

int main()
{
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
}
