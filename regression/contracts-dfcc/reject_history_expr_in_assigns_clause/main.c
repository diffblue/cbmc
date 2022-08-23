int foo(int *x) __CPROVER_assigns(__CPROVER_old(*x))
{
  return 0;
}

int main()
{
  int x;
  int ret = foo(&x);
  return 0;
}
