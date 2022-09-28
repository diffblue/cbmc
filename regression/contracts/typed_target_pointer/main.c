int foo(int *x, int *y)
  __CPROVER_assigns(__CPROVER_typed_target(x), __CPROVER_typed_target(*y))
{
  return 0;
}

int main()
{
  int x;
  int y;
  int ret = foo(&x, &y);
  return 0;
}
