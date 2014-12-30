#include <assert.h>

#ifdef __GNUC__
extern int foo(int);

extern inline int foo(int a)
{
  return 42;
}

int bar()
{
  return foo(0);
}

// this is not allowed with C99 or above
int foo(int a)
{
  return 0;
}
#endif

int main()
{
#ifdef __GNUC__
  assert(bar()==0);
  assert(foo(0)==0);
#endif
}

