int main()
{
  int i = 1;
  int j = i++ + i;
  __CPROVER_assert(j == 3, "j == 3");
  return 0;
}
