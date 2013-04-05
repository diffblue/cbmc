void foo()
{
  assert(0);
  __CPROVER_assume(0);
}

int main()
{
  __CPROVER_ASYNC_1: foo();
  __CPROVER_assume(0);
  return 0;
}
