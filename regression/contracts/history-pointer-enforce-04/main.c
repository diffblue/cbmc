void foo(int *x, int *y) __CPROVER_assigns(*x, *y)
  __CPROVER_ensures(*x == __CPROVER_old(*y) + 1 && *y == __CPROVER_old(*x) + 2)
{
  int x_initial = *x;
  *x = *y + 1;
  *y = x_initial + 2;
}

int main()
{
  int x, y;
  foo(&x, &y);

  return 0;
}
