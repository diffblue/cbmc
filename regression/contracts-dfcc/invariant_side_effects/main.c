#include <assert.h>
#include <stdlib.h>

int main()
{
  unsigned N, *a = malloc(sizeof(unsigned int));

  *a = 0;
  while(*a < N)
    // clang-format off
    __CPROVER_loop_invariant((0 <= *a) && (*a <= N))
    __CPROVER_decreases(N - *a)
    // clang-format on
    {
      ++(*a);
    }

  assert(*a == N);
}
