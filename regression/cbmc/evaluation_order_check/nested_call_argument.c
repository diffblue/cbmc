int p = 1;

int f(int x, int y)
{
  return x / 2 + y / 2;
}

int g(int x, int y)
{
  return x / y;
}

int main()
{
  int i = 10;
  int j = f(g(i, p), p--);
  __CPROVER_assert(j == 5, "j == 5");
  f(g(i, p), p--);
  return 0;
}
