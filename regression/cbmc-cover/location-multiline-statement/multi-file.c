#include <stdlib.h>

int foo(int x, int y)
{
  return x;
}

int main()
{
  int *ptr = malloc(sizeof(*ptr));

  // clang-format off
  foo(
    1,
#include "dereference.h"
    ptr);
  // clang-format on

  if(0)
  {
    *ptr = 0;
  }

  return 0;
}
