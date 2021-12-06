#include <assert.h>
#include <stdlib.h>

#define MAX_SIZE 64

void main()
{
  unsigned N;
  __CPROVER_assume(0 < N && N <= MAX_SIZE);

  int *a = malloc(N * sizeof(int));

  for(int i = 0; i < N; ++i)
    // clang-format off
    __CPROVER_assigns(i, __CPROVER_POINTER_OBJECT(a))
    __CPROVER_loop_invariant(
      (0 <= i) && (i <= N) &&
      (i != 0 ==> __CPROVER_exists {
        int k;
        // constant bounds for explicit unrolling with SAT backend
        (0 <= k && k <= MAX_SIZE) && (
          // the actual symbolic bound for `k`
          k < i && a[k] == 1
        )
      })
    )
    // clang-format on
    {
      a[i] = 1;
    }

  // clang-format off
  assert(
    N != 0 ==> __CPROVER_exists {
    int k;
    // constant bounds for explicit unrolling with SAT backend
    (0 <= k && k <= MAX_SIZE) && (
      // the actual symbolic bound for `k`
      k < N && a[k] == 1
    )
  });
  // clang-format on
}
