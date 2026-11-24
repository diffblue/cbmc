int counter;

static void worker(void)
{
  counter = 3;
}

int main()
{
  counter = 2;
__CPROVER_ASYNC_1:
  worker();
  __CPROVER_assert(counter == 2 || counter == 3, "counter");
  __CPROVER_assert(0, "WRONG (must FAIL)");
  return 0;
}
