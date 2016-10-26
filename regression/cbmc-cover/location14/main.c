#include <assert.h>

int foo (int iX, int iY)
{
  return iX + iY;
}

int main(void)
{
  int iN = 2 + 1;
  if (iN == 4)
    assert(foo(5,3)==8);
}
