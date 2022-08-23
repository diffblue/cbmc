#include <stdlib.h>

void foo(char *arr) __CPROVER_requires(__CPROVER_is_freeable(arr))
  __CPROVER_ensures(__CPROVER_was_freed(__CPROVER_old(arr), 1))
{
  free(arr);
}

int main()
{
  size_t size;
  char arr[size];
  foo(arr);
  return 0;
}
