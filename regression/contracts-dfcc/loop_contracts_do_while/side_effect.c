int global;

int foo()
{
  return 0;
}

int main()
{
  global = 0;
  int argc = 1;
  if(argc > 1)
  {
    do
      __CPROVER_assigns(global)
      {
        global = 1;
      }
    while(foo());
  }
  __CPROVER_assert(global == 0, "should be zero");

  return 0;
}
