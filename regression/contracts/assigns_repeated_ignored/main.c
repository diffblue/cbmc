int foo(int *x) __CPROVER_assigns(*x, *x)
{
  *x = *x + 0;
  return *x + 5;
}

int main()
{
  int n = 4;
  n = foo(&n);

  return 0;
}
