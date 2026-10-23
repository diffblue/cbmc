__CPROVER_thread_local int thread_local_var;

void thread(void)
{
  thread_local_var = 1;
}

int main(void)
{
__CPROVER_ASYNC_0:
  thread();
  thread_local_var = 2;
  return 0;
}
