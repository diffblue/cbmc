int f1(int *x1) __CPROVER_requires(*x1 > 1 && *x1 < 10000)
  __CPROVER_ensures(__CPROVER_return_value == *x1 + 2)
{
  return f2(x1) + 1;
}

int f2(int *x2) __CPROVER_requires(*x2 > 1 && *x2 < 10000)
  __CPROVER_ensures(__CPROVER_return_value == *x2 + 1)
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
