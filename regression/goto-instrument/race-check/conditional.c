int shared;
_Bool flag;

void thread(void)
{
  if(flag)
    shared = 1;
}

int main(void)
{
  flag = 1;
__CPROVER_ASYNC_0:
  thread();
  shared = 2;
  return 0;
}
