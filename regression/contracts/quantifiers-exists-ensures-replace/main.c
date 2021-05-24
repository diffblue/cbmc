#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>

#define MAX_LEN 128

// clang-format off
int f1(int *arr, int len)
  __CPROVER_ensures(
    len > 0 ==> __CPROVER_exists {
      int i;
      // test replacement with symbolic bound
      (0 <= i && i < len) && arr[i] == 0
    }
  )
// clang-format on
{
  // we are only checking for contract replacement
  return 0;
}

int main()
{
  int len;
  __CPROVER_assume(0 <= len && len <= MAX_LEN);

  int *arr = malloc(len * sizeof(int));

  f1(arr, len);

  bool found_zero = false;
  for(int i = 0; i <= MAX_LEN; i++)
  {
    if(i < len)
      found_zero |= (arr[i] == 0);
  }

  // clang-format off
  assert(len > 0 ==> found_zero);
  // clang-format on
}
