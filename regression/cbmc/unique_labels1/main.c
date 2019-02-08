#include <assert.h>

static int foo()
{
  assert(0);
}

void bar();

int main()
{
  foo();
  bar();
}
