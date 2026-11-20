int g;
int ptr_ok(int *x)
{
  g = 1; // side effect in a function called from a requires clause
  return *x < 5;
}
int foo(int *x)
  // clang-format off
  __CPROVER_requires(__CPROVER_is_fresh(x, sizeof(int)) && ptr_ok(x))
  __CPROVER_assigns(*x)
// clang-format on
{
  *x = 1;
  return 0;
}
int main()
{
  int *n;
  foo(n);
  return 0;
}
