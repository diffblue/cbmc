#include <assert.h>
#include <stdbool.h>
#include <stddef.h>

#define N 16

void main()
{
  int a[N];
  a[10] = 0;
  bool flag = true;
  for(size_t j = 0; j < N; ++j)
    // clang-format off
  __CPROVER_assigns(j, __CPROVER_object_whole(a))
  __CPROVER_loop_invariant(j <= N)
  __CPROVER_loop_invariant((j != 0) ==> __CPROVER_forall {
        int k;
        (0 <= k && k < N) ==> (a[k] == 1)
  })
    // clang-format on
    {
      for(size_t i = 0; i < N; ++i)
        // clang-format off
      __CPROVER_assigns(i, __CPROVER_object_whole(a))
      __CPROVER_loop_invariant(0 <= i && i <= N)
      __CPROVER_loop_invariant(__CPROVER_forall { int k; k < i ==> a[k] == 1 })

        // clang-format on
        {
          a[i] = 1;
        }
    }
  assert(a[10] == 1);
}
