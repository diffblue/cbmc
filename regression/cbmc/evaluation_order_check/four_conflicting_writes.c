int n;
int a(void)
{
  n = n * 2;
  return 0;
}
int b(void)
{
  n = n + 1;
  return 0;
}
int c(void)
{
  n = n * 3;
  return 0;
}
int d(void)
{
  n = n + 5;
  return 0;
}
int main()
{
  n = 1;
  int j = a() + b() + c() + d();
  /* left-to-right gives ((1*2)+1)*3+5 = 14; other orders differ */
  __CPROVER_assert(n == 14, "n == 14 regardless of order");
  return 0;
}
