int foo() __CPROVER_assigns(__CPROVER_return_value)
{
  return 0;
}

int main()
{
  int x = foo();
  return 0;
}
