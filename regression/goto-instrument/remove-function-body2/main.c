#include <assert.h>

int foo123()
{
  int a;
  assert(a > 0);
  return a;
}

int foox()
{
  int a;
  assert(a > 0);
  return a;
}

int bar()
{
  int b;
  assert(b > 0);
  return b;
}

int main()
{
  foo123();
  foox();
  bar();
}
