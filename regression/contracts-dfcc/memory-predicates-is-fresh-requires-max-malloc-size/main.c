#include <stdlib.h>

void foo(char *arr, size_t size)
  // clang-format off
__CPROVER_requires(__CPROVER_is_fresh(arr, size))
__CPROVER_assigns(__CPROVER_object_from(arr))
// clang-format on
{
  assert(__CPROVER_same_object(arr, arr + size));
  if(size > 0)
  {
    arr[0] = 0;
    arr[size - 1] = 0;
  }
}

int main()
{
  char *arr;
  size_t size;
  foo(arr, size);
}
