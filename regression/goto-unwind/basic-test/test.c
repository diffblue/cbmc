#include <assert.h>
#include <stdio.h>

int fib(int N)
{
  assert(N >= 0);
  int x = 0, y = 1;
  while(N--)
  {
    assert(N >= -1);
    int tmp = x;
    x = y;
    y += tmp;
  }
  return y;
}

int main(void)
{
  assert(fib(0) == 1);   // true
  assert(fib(10) == 55); // false
  assert(fib(10) == 89); // true
  return 0;
}
