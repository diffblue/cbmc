int g;

void set_g(void)
{
  g = 1; // side effect two calls away from the requires clause
}

int helper(int *x)
{
  set_g();
  return *x < 5;
}

int ptr_ok(int *x)
{
  return helper(x);
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
