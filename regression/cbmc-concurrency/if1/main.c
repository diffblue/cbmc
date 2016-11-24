int main()
{
  int a;
  __CPROVER_ASYNC_1:
    if(a)
      __CPROVER_assert(0, "x");
  return a;
}

