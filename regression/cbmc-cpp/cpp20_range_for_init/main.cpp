// C++20 init-statement in range-based for
int main()
{
  int arr[] = {1, 2, 3};
  int sum = 0;
  for(int s = 0; int x : arr)
  {
    sum += x;
  }
  __CPROVER_assert(sum == 6, "range for with init");
  return 0;
}
