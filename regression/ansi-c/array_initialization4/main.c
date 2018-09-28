#include <assert.h>

int foo(unsigned n)
{
  assert(n > 0);
  int A[n] = {1};
  return A[0];
}

int main()
{
  assert(foo(1) == 1);
}
