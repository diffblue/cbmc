int main()
{
  int sum = 0;
  for(int i = 0; i < 3; i++)
  {
    sum += i;
  }
  __CPROVER_assert(sum == 3, "sum should be 3");
  return 0;
}
