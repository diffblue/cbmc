int foo(int foo_a)
{
  __CPROVER_assert(foo_a != 2, "assertion");
}

int bar(int bar_a)
{
  foo(bar_a + 1);
  foo(bar_a + 2);
}

int main()
{
  bar(0);
}
