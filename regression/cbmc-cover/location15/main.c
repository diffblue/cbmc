#include <assert.h>
#include <math.h>

int foo (int iX, int iY)
{
  return iX + iY;
}

int main(void)
{
  double dX = sqrt(2);
  if (dX > 5)
  {
    __CPROVER_assume(0);
    assert(foo(5,3)==1);
  }    
}
