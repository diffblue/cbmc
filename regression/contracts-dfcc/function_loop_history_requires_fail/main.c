void bar(int *x) __CPROVER_assigns(*x)
  __CPROVER_requires(*x == __CPROVER_loop_entry(*x) + 5)
{
  *x = *x + 5;
}

int main()
{
  int n;
  foo(&n);

  return 0;
}
