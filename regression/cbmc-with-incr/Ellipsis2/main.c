#include <assert.h>

int foo(int a, ...)
{
  return a;
}

int main()
{
  char c;
  long l;

  if(c<l)
    l=foo(c, c);
  else
    l=foo(c, l);

  assert(c==l);

  return 0;
}
