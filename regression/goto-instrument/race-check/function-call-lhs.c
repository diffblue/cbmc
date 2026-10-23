int shared;

int source(void)
{
  return 42;
}

void writer(void)
{
  shared = 1;
}

int main(void)
{
__CPROVER_ASYNC_0:
  writer();
  shared = source();
  return 0;
}
