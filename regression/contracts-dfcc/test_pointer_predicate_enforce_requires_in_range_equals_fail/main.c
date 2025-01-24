void foo(int *x, int *y)
  // clang-format off
__CPROVER_requires(__CPROVER_is_fresh(x, sizeof(int)))
__CPROVER_requires(*x == 0)
__CPROVER_requires(
  __CPROVER_pointer_in_range_dfcc(x, y, x) &&
  __CPROVER_pointer_equals(y, x))
__CPROVER_assigns(*y)
__CPROVER_ensures(*y == 1)
__CPROVER_ensures(*x == 1)
// clang-format on
{
  *y = 1;
}

int main()
{
  int *x;
  int *y;
  foo(x, y);
  return 0;
}
