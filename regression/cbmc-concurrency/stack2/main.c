void foo(unsigned x)
{
  __CPROVER_assert(x <= 1, "");
}

int main()
{
  unsigned local_to_main;
  local_to_main %= 2;
  _Bool nondet1;
  if(nondet1)
  {
  __CPROVER_ASYNC_1:
    foo(local_to_main);
    return 0;
  }
}
