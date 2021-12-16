#include <stdlib.h>

#define MAX_LEN 10

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
  if(0 < len)
    arr[0] = 0;
  if(1 < len)
    arr[1] = 0;
  if(2 < len)
    arr[2] = 0;
  if(3 < len)
    arr[3] = 0;
  if(4 < len)
    arr[4] = 0;
  if(5 < len)
    arr[5] = 0;
  if(6 < len)
    arr[6] = 0;
  if(7 < len)
    arr[7] = 0;
  if(8 < len)
    arr[8] = 0;
  if(9 < len)
    arr[9] = 0;

  return 0;
}

int main()
{
  int len;
  __CPROVER_assume(0 < len && len <= MAX_LEN);

  int *arr = malloc(len * sizeof(int));
  f1(arr, len);
}
