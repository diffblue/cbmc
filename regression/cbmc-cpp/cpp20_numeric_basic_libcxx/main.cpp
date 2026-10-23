// C++20 <numeric> header
#include <numeric>
int main()
{
  int arr[] = {1, 2, 3, 4, 5};
  int sum = std::accumulate(arr, arr + 5, 0);
  __CPROVER_assert(sum == 15, "accumulate");
}
