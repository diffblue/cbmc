int g;

void handler(int x)
{
  __CPROVER_assert(x == 3, "argument bound to x");
  g = x;
}

void callee(void (*fp)())
  // clang-format off
  __CPROVER_requires(fp == handler)
  __CPROVER_assigns(g)
// clang-format on
{
  // a call through a pointer to a function without a prototype (which is
  // variadic in the goto program) to a function with a prototype
  fp(3);
}

int main(void)
{
  callee(handler);
  return 0;
}
