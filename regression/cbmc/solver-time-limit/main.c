int main()
{
  int x = 1;
  __CPROVER_assert(x == 1, "trivially true");
  return 0;
}
