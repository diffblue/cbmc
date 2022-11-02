#include "header.h"

int main()
{
  int *n = malloc(sizeof(*n));
  *n = foo(n);

  return 0;
}
