int shared;

void writer(void)
{
  shared = 42;
}

int main(void)
{
__CPROVER_ASYNC_0:
  writer();
  // Shared read inside an ASSUME condition (exercises the is_assume() path).
  __CPROVER_assume(shared != 0);
  return 0;
}
