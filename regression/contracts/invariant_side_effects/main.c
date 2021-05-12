#include <assert.h>
#include <stdlib.h>

int main()
{
  unsigned N, *a = malloc(sizeof(unsigned int));

  *a = 0;
  while(*a < N)
    __CPROVER_loop_invariant((0 <= *a) && (*a <= N))
    {
      ++(*a);
    }

  assert(*a == N);
}
