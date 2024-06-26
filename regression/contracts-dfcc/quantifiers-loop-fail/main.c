#include <assert.h>
#include <stdbool.h>

#define N 16

void main()
{
  int a[N];
  a[10] = 0;
  bool flag = true;
  for(int j = 0; j < N; ++j)
    __CPROVER_loop_invariant(j <= N)
    {
      for(int i = 0; i < N; ++i)
        // clang-format off
        __CPROVER_assigns(i, __CPROVER_object_whole(a))
        __CPROVER_loop_invariant((0 <= i) && (i <= N) && __CPROVER_forall {
          int k;
          (0 <= k && k <= N) ==> (k<i ==> a[k] == 1)
        })
        // clang-format on
        {
          a[i] = 1;
        }
    }
  assert(a[10] == 1);
}
