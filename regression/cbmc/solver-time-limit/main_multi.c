int main()
{
  int a;
  // Each failing property is found in a solver call of its own.
  if(a == 1)
    __CPROVER_assert(0, "a is not 1");
  if(a == 2)
    __CPROVER_assert(0, "a is not 2");
  __CPROVER_assert(a + 0 == a, "holds");
  return 0;
}
