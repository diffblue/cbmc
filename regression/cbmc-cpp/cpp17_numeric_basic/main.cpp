#include <cassert>
#include <numeric>
int main()
{
  int arr[] = {1, 2, 3, 4};
  int sum = std::accumulate(arr, arr + 4, 0);
  assert(sum == 10);
  return 0;
}
