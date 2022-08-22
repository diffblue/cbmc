#include <stdlib.h>
int main()
{
  size_t size = 10;
  char *arr = malloc(size);

  for(size_t i = 0; i <= size; i++)
    // clang-format off
  __CPROVER_assigns(i, arr[2], __CPROVER_POINTER_OBJECT(arr))
  __CPROVER_frees(arr)
    // clang-format on2
    {
      if(i == 2)
        arr[i] = 0;
      if(i == size)
        free(arr);
    }
  return 0;
}
