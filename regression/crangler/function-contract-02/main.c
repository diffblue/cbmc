int foo(int *x)
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
