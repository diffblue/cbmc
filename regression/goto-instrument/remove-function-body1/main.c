#include <assert.h>

int foo()
{
  int a;
  assert(a>0);
  return a;
}

int bar()
{
  int b;
  assert(b>0);
  return b;
}

int main()
{
  foo();
  bar();
}
