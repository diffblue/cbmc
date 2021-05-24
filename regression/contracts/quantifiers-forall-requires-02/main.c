#include <stdlib.h>

#define MAX_LEN 16

// clang-format off
int f1(int *arr, int len)
  __CPROVER_requires(__CPROVER_forall {
    int i;
    // test replacement with symbolic bound
    (0 <= i && i < len) ==> arr[i] == i
  })
  __CPROVER_ensures(
    __CPROVER_return_value == 0
  )
// clang-format on
{
  return 0;
}

int main()
{
  int len;
  __CPROVER_assume(0 <= len && len <= MAX_LEN);

  int *arr = malloc(len * sizeof(int));
  for(int i = 0; i < MAX_LEN; ++i)
  {
    if(i < len)
      arr[i] = i;
  }

  f1(arr, len);
}
