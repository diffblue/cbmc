// C++20 <algorithm> header
#include <algorithm>
int main()
{
  int arr[] = {3, 1, 4, 1, 5};
  std::sort(arr, arr + 5);
  __CPROVER_assert(arr[0] == 1, "sorted");
}
