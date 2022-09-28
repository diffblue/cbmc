int foo(int *x) __CPROVER_requires(__CPROVER_old(*x))
{
  return 0;
}

int main()
{
  int x;
  int retval = foo(&x);
  return 0;
}
