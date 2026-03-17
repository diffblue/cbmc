#include <cassert>
int main()
{
  int arr[] = {1, 2, 3};
  int sum = 0;
  for(int x : arr)
    sum += x;
  assert(sum == 6);
  return 0;
}
