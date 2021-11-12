#include <stdlib.h>

#define MAX_LEN 16

// clang-format off
int f1(int *arr, int len)
  __CPROVER_assigns(__CPROVER_POINTER_OBJECT(arr))
  __CPROVER_ensures(__CPROVER_forall {
    int i;
    // test enforcement with symbolic bound
    (0 <= i && i < len) ==> arr[i] == 0
  })
// clang-format on
{
  for(int i = 0; i < MAX_LEN; i++)
  {
    if(i < len)
      arr[i] = 0;
  }
  return 0;
}

int main()
{
  int len;
  __CPROVER_assume(0 < len && len <= MAX_LEN);

  int *arr = malloc(len * sizeof(int));
  f1(arr, len);
}
