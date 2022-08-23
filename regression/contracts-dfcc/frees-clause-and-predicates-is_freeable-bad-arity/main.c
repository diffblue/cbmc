#include <stdlib.h>

void foo(char *arr) __CPROVER_requires(__CPROVER_is_freeable(arr, 1))
{
}

int main()
{
  size_t size;
  char arr[size];
  foo(arr);
  return 0;
}
