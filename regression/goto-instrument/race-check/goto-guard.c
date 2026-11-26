int shared;

void writer(void)
{
  shared = 42;
}

int main(void)
{
__CPROVER_ASYNC_0:
  writer();
  if(shared)
  {
  }
  return 0;
}
