int global;

void thread()
{
  int local;
  local=global; // #6
  if(local==3)
  {
    global=1;   // #7
  }
}

int main()
{
  __CPROVER_ASYNC_1: thread();
  global=2;                   // #2
  assert(global!=3); // safe  // #4
  global=3;                   // #5
}

