#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>

int baz(int *x) __CPROVER_assigns(__CPROVER_POINTER_OBJECT())
{
  *x = 0;
  return 0;
}

int main()
{
  int x;
  baz(&x);
}
