void f1(int *x) __CPROVER_assigns(*x)
{
  int *a = x;
  *a = 5;
}

int main()
{
  int n = 3;
  f1(&n);

  return 0;
}
