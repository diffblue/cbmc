int global;

void thread()
{
  global=1;
  global=2;
}

int main()
{
  __CPROVER_ASYNC_1: thread();

  if(global==2)
  {
    assert(global!=1);
  }
}
