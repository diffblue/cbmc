#include <assert.h>

int foo (int iX, int iY)
{
  return iX + iY;
  __CPROVER_assume(0);
}

int main(void)
{
  assert(foo(5,3)==8);
}
