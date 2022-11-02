void foo(int *x) __CPROVER_assigns(*x)
  __CPROVER_ensures(*x == __CPROVER_old(*x) + 5)
{
  *x = *x + 5;
}

int main()
{
  int n;
  foo(&n);

  return 0;
}
