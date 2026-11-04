int n;
int f(void)
{
  n = 1;
  return 0;
}
int g(void)
{
  n = 2;
  return 0;
}
int main()
{
  int j = f() + g();
  __CPROVER_assert(n == 2, "n == 2 regardless of evaluation order");
  return 0;
}
