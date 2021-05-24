#include <stdlib.h>

#define MAX_LEN 8

// clang-format off
int f1(int *arr, int len)
  __CPROVER_requires(__CPROVER_forall {
    int i;
    // constant bounds for explicit unrolling with SAT backend
    (0 <= i && i < MAX_LEN) ==> (
      // actual symbolic bound for `i`
      i < len ==> arr[i] == 0
    )
  })
  __CPROVER_ensures(__CPROVER_forall {
    int i;
    // positive context, so symbolic bounds are fine
    (0 <= i && i < len) ==> arr[i] == 0
  })
// clang-format on
{
  return 0;
}

int main()
{
  int len;
  __CPROVER_assume(0 <= len && len <= MAX_LEN);

  int *arr = malloc(len);
  for(int i = 0; i < MAX_LEN; ++i)
  {
    if(i < len)
      arr[i] = 0;
  }

  f1(arr, len);
}
