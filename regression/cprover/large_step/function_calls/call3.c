int bar()
{
  return 10;
}

int foo()
{
  return bar();
}

int main()
{
  int x;
  x = foo();
  __CPROVER_assert(x == 10, "property 1"); // should pass
}
