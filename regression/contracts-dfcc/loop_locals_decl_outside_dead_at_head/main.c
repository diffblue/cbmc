#include <stdbool.h>

bool nondet_bool();

void main()
{
  unsigned i = 0, sum = 0;
  unsigned x;
  while(i < 10)
    // clang-format off
    __CPROVER_assigns(i, sum)
    __CPROVER_loop_invariant(i <= 10 && sum <= 2 * i)
    // clang-format on
    {
      x = nondet_bool() ? 2 : 0;
      sum += x;
      i += 1;
    }
  __CPROVER_assert(sum <= 20, "sum <= 20");
}
