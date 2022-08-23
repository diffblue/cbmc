int z;

// z is not assigned, but it *may* be assigned.
// The assigns clause does not need to exactly match the
// set of variables which are assigned in the function.
int foo(int *x) __CPROVER_assigns(z, *x)
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
