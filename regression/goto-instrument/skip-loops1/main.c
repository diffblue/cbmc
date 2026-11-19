int main()
{
  int x = 0;
  for(int i = 0; i < 3; ++i)
    x++;
  __CPROVER_assert(x == 3, "the loop runs three times");
  __CPROVER_assert(x == 0, "the loop is skipped");
  return 0;
}
