int global;

int main()
{
  global = 0;
  int argc = 1;
  do
  {
    int local;
    global = 1;
    local = 1;
    for(int i = 0; i < 1; i++)
    {
      local = 1;
      global = 2;
      int j = 0;
      while(j < 1)
      {
        local = 1;
        global = 3;
        j++;
      }
      __CPROVER_assert(global == 3, "case3");
    }
    __CPROVER_assert(global == 3, "case3");
  } while(0);
  __CPROVER_assert(global == 3, "case1");
  return 0;
}
