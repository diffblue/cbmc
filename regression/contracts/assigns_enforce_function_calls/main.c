int *bar(int *x)
{
  return *x;
}

int foo(int *x) __CPROVER_assigns(bar(x))
{
  *x = 0;
  return 0;
}

int main()
{
  int x;
  foo(&x);
  baz(&x);
}
