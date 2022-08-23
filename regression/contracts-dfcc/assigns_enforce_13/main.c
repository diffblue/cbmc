void f1(int *x, int *y) __CPROVER_assigns(*y)
{
  int *a = x;
  *a = 5;
}

int main()
{
  int m = 3;
  int n = 3;
  f1(&n, &m);

  return 0;
}
