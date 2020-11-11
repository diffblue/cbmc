int main()
{
  int x;
  __CPROVER_assert(x == 42, "should fail");
  return 0;
}
