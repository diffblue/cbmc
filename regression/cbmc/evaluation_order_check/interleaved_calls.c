int n;

int a(void)
{
  n = n * 10 + 1;
  return 0;
}

int b(void)
{
  n = n * 10 + 2;
  return 0;
}

int c(void)
{
  n = n * 10 + 3;
  return 0;
}

int main()
{
  int j = (a() + b()) * c();
  __CPROVER_assert(n != 132, "c() executes between a() and b()");
  __CPROVER_assert(n != 213 && n != 231, "b() executes before a()");
  return 0;
}
