#include <assert.h>

int foo(int a)
{
  return a;
}

// this is a GCC extension
#ifdef __GNUC__
int bar(int b) __attribute__((alias("foo")));

__typeof__(foo) bar2 __attribute__((alias("foo")));
#endif

int main()
{
  #ifdef __GNUC__
  assert(bar(42)==42);
  assert(bar2(42)==42);
  #endif
  return 0;
}
