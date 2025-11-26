#include <assert.h>

int foo(int x)
{
  return x + 1;
}

int main()
{
  int result = foo(5);
  assert(result == 6);
  return 0;
}
