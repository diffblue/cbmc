int g;
int two();

void callee(void)
  // clang-format off
  __CPROVER_assigns(g)
// clang-format on
{
  two(3);
}

int two(a, b) int a, b;
{
  g = a;
  return a;
}

int main(void)
{
  callee();
  return 0;
}
