int main()
{
  int x;
  __CPROVER_assume(x == 1);
  __CPROVER_assert(x == 1, "trivially true");
  return 0;
}
