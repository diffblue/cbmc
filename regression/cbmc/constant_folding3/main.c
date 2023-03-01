int main(void)
{
  int x;
  int plus_one_is_null = &x + 1 == (int *)0 ? 1 : 0;
  __CPROVER_assert(plus_one_is_null != 2, "cannot be 2");

  return 0;
}
