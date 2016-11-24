#include <assert.h>

int foo(int * a)
{
  *a=42;
  return 0;
}

int main()
{
  int x=(foo(&x),x);
  assert(x==42);
  return x;
}
