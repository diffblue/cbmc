#include <assert.h>

int foo(int a, ...)
{
  return a;
}

int main()
{
  char c = __VERIFIER_nondet_char();
  long l = __VERIFIER_nondet_long();

  if(c<l)
    l=foo(c, c);
  else
    l=foo(c, l);

  assert(c==l);

  return 0;
}
