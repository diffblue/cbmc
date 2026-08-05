int p = 5;

int f(int x)
{
  p = 0;
  return x / 2;
}

int main()
{
  int i = 10;
  int j = f(i) + i / p;
  __CPROVER_assert(j == 7, "j == 7");
  return 0;
}
