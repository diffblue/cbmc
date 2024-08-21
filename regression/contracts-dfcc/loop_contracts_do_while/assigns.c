int global;

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
    while(0);
  }
  __CPROVER_assert(global == 0, "should be zero");

  return 0;
}
