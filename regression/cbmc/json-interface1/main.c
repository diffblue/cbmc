void foo(int x)
{
  for(int i = 0; i < 5; ++i)
  {
    if(x)
      __CPROVER_assert(0, "assertion 0");
    __CPROVER_assert(0, "assertion 0");
  }
  __CPROVER_assert(0, "assertion 0");
}
