#include <assert.h>

void int_test()
{
  int *p, v = __VERIFIER_nondet_int(), x = __VERIFIER_nondet_int(), x_before;
  x_before = x;
  p = &x;

  int result = __atomic_add_fetch(p, v = __VERIFIER_nondet_int(), 0);
  assert(result == x);
  assert(x == x_before + v);
}

void long_test()
{
  long *p, v = __VERIFIER_nondet_long(), x = __VERIFIER_nondet_long(), x_before;
  x_before = x;
  p = &x;

  long result = __atomic_add_fetch(p, v, 0);
  assert(result == x);
  assert(x == x_before + v);
}

void mixed_test()
{
  int *p, x = __VERIFIER_nondet_int(), x_before;
  long v = __VERIFIER_nondet_long();
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
