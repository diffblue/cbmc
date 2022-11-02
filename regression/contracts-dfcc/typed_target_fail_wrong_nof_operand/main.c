int foo(int x, int y) __CPROVER_assigns(__CPROVER_typed_target(x, y))
{
  return 0;
}

int main()
{
  int ret = foo(1, 2);
  return 0;
}
