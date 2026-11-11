int g;

int my_log(int n, ...)
  // clang-format off
  __CPROVER_requires(n == 1)
  __CPROVER_assigns(g)
// clang-format on
{
  g = n;
  __CPROVER_assert(0, "body is reachable");
  return 0;
}

int main(void)
{
  my_log(1, 42);
  return 0;
}
