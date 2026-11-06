int foo(int *x) __CPROVER_assigns(*x) __CPROVER_ensures(*x == 42)
{
  *x = 42;
  return 0;
}

int bar(int *y) __CPROVER_assigns(*y) __CPROVER_ensures(*y == 7)
{
  *y = 7;
  return 0;
}

int main(void)
{
  int u, v;
  foo(&u);
  bar(&v);
  return 0;
}
