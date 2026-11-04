int p, q, r, s;
int a(void)
{
  p = 1;
  return 1;
}
int b(void)
{
  q = 2;
  return 2;
}
int c(void)
{
  r = 3;
  return 3;
}
int d(void)
{
  s = 4;
  return 4;
}
int main()
{
  int j = a() + b() + c() + d();
  __CPROVER_assert(j == 10 && p + q + r + s == 10, "order independent");
  return 0;
}
