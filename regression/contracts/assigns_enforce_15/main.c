int global = 0;

int foo(int *x) __CPROVER_assigns(*x)
  __CPROVER_ensures(__CPROVER_return_value == *x + 5)
{
  int z = 5;
  int y = bar(&z);
  return *x + 5;
}

int bar(int *a) __CPROVER_ensures(__CPROVER_return_value >= 5)
{
  *a = *a + 2;
  return *a;
}

int baz() __CPROVER_ensures(__CPROVER_return_value == global)
{
  global = global + 1;
  return global;
}

void qux(void) __CPROVER_assigns()
{
  global = global + 1;
}

int main()
{
  int n;
  n = foo(&n);
  n = baz();
  qux();
  return 0;
}
