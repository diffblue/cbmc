int main(void)
{
  int x;
  __CPROVER_assume(x < 10);
  __CPROVER_assert(x != 0, "");
  return 0;
}
