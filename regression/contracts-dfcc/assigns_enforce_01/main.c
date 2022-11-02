int foo(int *x) __CPROVER_assigns(*x)
  __CPROVER_ensures(__CPROVER_return_value == *x + 5)
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
