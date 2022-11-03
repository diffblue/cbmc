int f1(int *x1)
{
  return f2(x1) + 1;
}

int f2(int *x2)
{
  return *x2 + 1;
}

int main()
{
  int p;
  __CPROVER_assume(p > 1 && p < 10000);
  f1(&p);

  return 0;
}
