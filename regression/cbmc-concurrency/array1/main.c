int data[2];
unsigned sync;

void thread()
{
  data[sync % 2] = 1;
  __CPROVER_assert(data[sync % 2] == 1, "1");
}

int main()
{
  unsigned nondet;
  sync = nondet;
__CPROVER_ASYNC_1:
  thread();
  unsigned sync_value = sync;
  data[(sync_value + 1) % 2] = 2;
  __CPROVER_assert(data[(sync_value + 1) % 2] == 2, "2");
}
