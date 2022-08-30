#include <stdlib.h>
int main()
{
  size_t size = 10;
  char *arr = malloc(size);
  size_t i = 0;
  while(i <= size)
    // clang-format off
  __CPROVER_assigns(i, arr[2], __CPROVER_POINTER_OBJECT(arr))
  __CPROVER_frees(arr[2])
    // clang-format on
    {
      if(i == 2)
        arr[i] = 0;
      if(i == size)
        free(arr);
      i++;
    }
  return 0;
}
