#define N 2000
int nondet_int();
int b[N];
int main()
{
  int x = nondet_int();
  // a is an array literal, b is zero-initialised and then updated
  int a[N] = {x};
  b[0] = x;
  __CPROVER_assert(__CPROVER_equal(a, b), "equal");
  return 0;
}
