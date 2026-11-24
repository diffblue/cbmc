int g;

int post_ok(int r)
{
  g = 1; // side effect in a function called from an ensures clause
  return r == 0;
}

int foo(void)
  // clang-format off
  __CPROVER_ensures(post_ok(__CPROVER_return_value))
// clang-format on
{
  return 0;
}

int main()
{
  foo();
  return 0;
}
