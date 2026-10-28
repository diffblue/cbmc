int nondet_int();
int main()
{
  int x = nondet_int(), y = nondet_int(), z = nondet_int();
  __CPROVER_assume(y == z + 0 * x);
  int a[2] = {x, y};
  int b[2] = {x, z};
  __CPROVER_assert(
    __CPROVER_equal(a, b), "arrays with equal elements are equal");
  return 0;
}
