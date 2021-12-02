int n=0;

void thread()
{
  __CPROVER_atomic_begin();
  ++n;
  __CPROVER_atomic_end();
}

int main()
{
  int x;

  if(x)
  {
__CPROVER_ASYNC_1: thread();
  }

__CPROVER_ASYNC_2: thread();
__CPROVER_ASYNC_3: thread();

  __CPROVER_assert(n<4, "3 threads spawned");

  return 0;
}
