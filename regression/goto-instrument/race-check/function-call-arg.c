int shared;

void sink(int val)
{
  (void)val;
}

void writer(void)
{
  shared = 42;
}

int main(void)
{
__CPROVER_ASYNC_0:
  writer();
  sink(shared);
  return 0;
}
