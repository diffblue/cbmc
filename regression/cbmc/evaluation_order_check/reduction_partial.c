int x, n;

int f(void)
{
  x = 1;
  return 0;
}

int g(void)
{
  n = n + 1;
  return 0;
}

int main()
{
  int j = x + f() + g();
  __CPROVER_assert(n == 1, "g executes once");
  return j;
}
