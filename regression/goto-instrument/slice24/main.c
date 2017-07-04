#include <assert.h>

int x;

void f1()
{
  int y=0;
  y++;
}

void f2()
{
  x++;
}

int main()
{
  f1();
  f2();
  assert(x==1);
  return 0;
}
