void writer(int *p)
{
  *p = 42;
}

int main(void)
{
  int local = 0;
__CPROVER_ASYNC_0:
  writer(&local);
  local = 1;
  return 0;
}
