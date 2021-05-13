void foo(int *x, int *y) __CPROVER_assigns(*x, *y)
  __CPROVER_ensures(*x == __CPROVER_old(*x) + 2 || *y == __CPROVER_old(*y) + 3)
{
  *x = *x + 1;
  *y = *y + 2;
}

int main()
{
  int x, y;
  foo(&x, &y);

  return 0;
}
