#include <math.h>

int foo (int iX, int iY)
{
  return iX + iY;
}

int main(void)
{
  double dX=sqrt(2);
  if(dX>5)
  {
    __CPROVER_assume(0);
    foo(5, 3);
  }    
}
