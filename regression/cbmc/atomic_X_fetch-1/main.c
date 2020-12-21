#include <assert.h>

void int_test()
{
  int *p, v, x, x_before;
  x_before = x;
  p = &x;

  int result = __atomic_add_fetch(p, v, 0);
  assert(result == x);
  assert(x == x_before + v);
}

void long_test()
{
  long *p, v, x, x_before;
  x_before = x;
  p = &x;

  long result = __atomic_add_fetch(p, v, 0);
  assert(result == x);
  assert(x == x_before + v);
}

void mixed_test()
{
  int *p, x, x_before;
  long v;
  x_before = x;
  p = &x;

  int result = __atomic_add_fetch(p, v, 0);
  assert(result == x);
  assert(x == x_before + (int)v);
}

int main()
{
  int_test();
  long_test();
  mixed_test();

  return 0;
}
