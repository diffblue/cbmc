int foo() __CPROVER_requires(__CPROVER_return_value == 0)
{
  return 0;
}

int main()
{
  int x = foo();
  return 0;
}
