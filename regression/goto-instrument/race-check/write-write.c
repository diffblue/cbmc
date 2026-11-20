int shared;

void thread(void)
{
  shared = 1;
}

int main(void)
{
__CPROVER_ASYNC_0:
  thread();
  shared = 2;
  return 0;
}
