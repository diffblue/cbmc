#include <assert.h>
#include <limits.h>
#include <stdbool.h>

bool check(unsigned *i, unsigned *j, unsigned *k)
{
  (*j)++;
  return *i < *k;
}

int main()
{
  unsigned i, j, k;
  __CPROVER_assume(k < UINT_MAX);

  i = j = 0;

  while(check(&i, &j, &k))
    // clang-format off
    __CPROVER_assigns(i, j)
    __CPROVER_loop_invariant(0 <= i && i == j && i <= k)
    // clang-format on
    {
      i++;
    }

  assert(i == k);
  assert(j == k + 1);
}
