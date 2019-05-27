int nondet_foo()
{
  return 42;
}

int main()
{
  int x = nondet_foo();
  __CPROVER_assert(x == 42, "nondet_foo returns a constant");
}
