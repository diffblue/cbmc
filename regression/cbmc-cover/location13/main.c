#include <assert.h>

int myfunc(int a, int b)
{
  return a+b;
}

int foo (int iX, int iY)
{
  return iX + iY;
  assert(myfunc(iX,iY)==8);
}

int main(void)
{
  assert(foo(5,3)==8);
}
