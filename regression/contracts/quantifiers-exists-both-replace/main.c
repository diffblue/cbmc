#include <stdlib.h>

#define MAX_LEN 8

// clang-format off
int f1(int *arr, int len)
  __CPROVER_requires(
    len > 0 ==> __CPROVER_exists {
      int i;
      // constant bounds for explicit unrolling with SAT backend
      (0 <= i && i < MAX_LEN) && (
        // actual symbolic bound for `i`
        i < len && arr[i] == 0
      )
    }
  )
  __CPROVER_ensures(
    len > 0 ==> __CPROVER_exists {
      int i;
      // constant bounds for explicit unrolling with SAT backend
      (0 <= i && i < MAX_LEN) && (
        // actual symbolic bound for `i`
        i < len && arr[i] == 0
      )
    }
  )
// clang-format on
{
  return 0;
}

int main()
{
  int len;
  __CPROVER_assume(0 <= len && len <= MAX_LEN);

  int *arr = malloc(len);
  if(len > 0)
    arr[0] = 0;

  f1(arr, len);
}
