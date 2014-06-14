#include <assert.h>

// the following function collides
static int f()
{
  int local=1;
  return local;
}

int f1()
{
  return f();
}

int f2();

int main()
{
  assert(f1()==1);
  assert(f2()==2);
}
