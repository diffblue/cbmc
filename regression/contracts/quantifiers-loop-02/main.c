#include <assert.h>

void main()
{
  int N, a[64];
  __CPROVER_assume(0 <= N && N < 64);

  for(int i = 0; i < N; ++i)
    // clang-format off
    __CPROVER_loop_invariant(
      (0 <= i) && (i <= N) &&
      __CPROVER_forall {
        int k;
        (0 <= k && k < i) ==> a[k] == 1
      }
    )
    // clang-format on
    {
      a[i] = 1;
    }

  // clang-format off
  assert(__CPROVER_forall {
    int k;
    (0 <= k && k < N) ==> a[k] == 1
  });
  // clang-format on

  int k;
  __CPROVER_assume(0 <= k && k < N);
  assert(a[k] == 1);
}
