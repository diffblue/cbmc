int f(int x)
{
  return x + 1;
}
int g(int y)
{
  return y * 2;
}
int main()
{
  int a = 1, b = 2;
  int j = f(a) + g(b);
  __CPROVER_assert(j == 6, "j");
  return 0;
}
