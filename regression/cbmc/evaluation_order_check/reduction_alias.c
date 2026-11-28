int x;

int f(int *p)
{
  *p = 1;
  return 0;
}

int g(void)
{
  return x;
}

int main()
{
  int j = f(&x) + g();
  __CPROVER_assert(j == 0, "g executes before f");
  return 0;
}
