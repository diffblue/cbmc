inline void foo(int x)
{
}

void bar()
{
  foo(0);
}

void foobar()
{
  // different argument values must not cause an inconsistency in the
  // equation system
  foo(0);
  bar();
  foo(1);
}

int main()
{
  foobar();
  foobar();
  __CPROVER_assert(0, "");
  return 0;
}
