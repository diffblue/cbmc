int n = 0;

int f(void)
{
  n = n + 1;
  return 0;
}

int g(void)
{
  n = n * 2;
  return 0;
}

void h(int a, int b)
{
}

int h2(int a, int b)
{
  return a + b;
}

int z;

int main()
{
  h(f(), g());
  __CPROVER_assert(n == 1, "f and g evaluated right-to-left");

  /* the same order must apply when the call is the right-hand side of a
     plain assignment statement, which takes a different lowering path */
  n = 0;
  z = h2(f(), g());
  __CPROVER_assert(n == 1, "f and g evaluated right-to-left in assignment");
  return 0;
}
