int foo(int *x) __CPROVER_assigns(*x) __CPROVER_ensures(*x == 42)
{
  *x = 42;
  return 0;
}

int main(void)
{
  int v;
  foo(&v);
  return 0;
}
