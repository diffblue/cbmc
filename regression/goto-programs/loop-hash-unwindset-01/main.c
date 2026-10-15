int main()
{
  int arr[5] = {1, 2, 3, 4, 5};
  int sum = 0;
  for(int i = 0; i < 5; i++)
  {
    sum += arr[i];
  }
  __CPROVER_assert(sum == 15, "sum should be 15");
  return 0;
}
