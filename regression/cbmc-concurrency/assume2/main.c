int g;

int foo()
{
  __CPROVER_assume(g);
  assert(0);
}

int main()
{
  __CPROVER_ASYNC_1: foo();
  return 0;
}
