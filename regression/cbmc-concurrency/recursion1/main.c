void rec_spawn()
{
__CPROVER_ASYNC_1: rec_spawn();
}

int main()
{
start:
  (void)0;
__CPROVER_ASYNC_1:
  ({(void)0;
  goto start;});

start2:
  (void)0;
__CPROVER_ASYNC_2:
  goto start2;

  rec_spawn();

  __CPROVER_assert(0, "should be reachable when using --partial-loops");

  return 0;
}
