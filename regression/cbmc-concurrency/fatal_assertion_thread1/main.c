int shared;
int other;

void worker(void)
{
  int divisor = shared;
  // division by zero: undefined behaviour in this thread
  shared = 10 / divisor;
}

void bystander(void)
{
  // may run after the undefined behaviour in the worker thread
  __CPROVER_assert(other == 0, "bystander");
}

int main()
{
  __CPROVER_assert(other == 0, "before any thread");
__CPROVER_ASYNC_1:
  bystander();
__CPROVER_ASYNC_2:
  worker();
  // not reachable from the worker thread, but may run after its undefined
  // behaviour
  __CPROVER_assert(other == 0, "after the spawn");
  return 0;
}
