int shared;

void thread(void)
{
  shared = 1;
}

int main(void)
{
  int local;
__CPROVER_ASYNC_0:
  thread();
  local = shared;
  return 0;
}
