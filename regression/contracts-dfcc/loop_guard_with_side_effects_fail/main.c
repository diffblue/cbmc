#include <assert.h>
#include <stdbool.h>

bool check(unsigned *i, unsigned *j, unsigned *k)
{
  (*j)++;
  return *i < *k;
}

int main()
{
  unsigned i, j, k;

  i = j = 0;

  while(check(&i, &j, &k))
    // clang-format off
    __CPROVER_assigns(i)
    __CPROVER_loop_invariant(0 <= i && i <= k)
    // clang-format on
    {
      i++;
    }

  assert(i == k);
}
