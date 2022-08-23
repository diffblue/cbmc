void foo(int a) __CPROVER_assigns(0)
{
  a = 0;
}

int main()
{
  int n;
  foo(n);
  return 0;
}
