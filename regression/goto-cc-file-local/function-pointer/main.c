#include <assert.h>

static int foo()
{
  return 3;
}

int (*fptrs[])(void) = {foo};

int main()
{
  int x = fptrs[0]();
  assert(x == 3);
}
