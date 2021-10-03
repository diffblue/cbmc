#include <assert.h>
#include <stdlib.h>

static int x;

void foo() __CPROVER_assigns(x)
{
  int *y = &x;

  static int x;
  x++;

  (*y)++;
}

int main()
{
  foo();
}
