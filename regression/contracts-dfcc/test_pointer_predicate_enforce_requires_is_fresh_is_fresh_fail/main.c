void foo(int *x)
  // clang-format off
__CPROVER_requires(
  __CPROVER_is_fresh(x, sizeof(int)) && __CPROVER_is_fresh(x, sizeof(int)))
__CPROVER_assigns(*x)
__CPROVER_ensures(*x == 0)
// clang-format on
{
  *x = 0;
}

int main()
{
  int *x;
  foo(x);
  return 0;
}
