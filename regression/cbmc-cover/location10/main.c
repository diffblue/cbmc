#include <assert.h>

int myfunc(int x, int y)
{
  int z = x + y;
  return z;
}

int main(void)
{
  _Bool x=0, y;
  if (x)
    assert(myfunc(2,3)==5);
  else
    y=1;

  if (y)
    assert(myfunc(4,3)==7);
  else 
    assume(0);

  assert(y==1);
}
