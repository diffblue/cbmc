int foo(int parameter)
{
  return parameter + 1;
}

int main()
{
  int x;
  x = foo(123);
  __CPROVER_assert(0, "property 1");
}
