int shared;

int get_shared(void)
{
  return shared;
}

void writer(void)
{
  shared = 42;
}

int main(void)
{
  int local;
__CPROVER_ASYNC_0:
  writer();
  local = get_shared();
  return 0;
}
