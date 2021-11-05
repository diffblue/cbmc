#include <assert.h>
#include <stdlib.h>

static int x;
static int xx;

void foo()
{
  int *y = &x;
  int *yy = &xx;

  static int x;
  // must pass (modifies local static)
  x++;

  // must pass (modifies assignable global static )
  (*y)++;

  // must fail (modifies non-assignable global static)
  (*yy)++;
}

void bar() __CPROVER_assigns(x)
{
  foo();
}

int main()
{
  bar();
}
