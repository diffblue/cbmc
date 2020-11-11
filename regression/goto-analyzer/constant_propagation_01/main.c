#include <assert.h>

int main()
{
  int i, j=20;

  if (j==20)
  {
    int x=1,y=2,z;
    z=x+y;
    __CPROVER_assert(z == 3, "z==3");
  }
}
