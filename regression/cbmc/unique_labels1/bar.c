#include <assert.h>

static int foo()
{
  assert(1 < 0);
}

void bar()
{
  foo();
}
