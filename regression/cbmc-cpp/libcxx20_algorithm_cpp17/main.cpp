// libc++-20's <algorithm> in C++17 mode.
#include <algorithm>
#include <cassert>
int main()
{
  int arr[] = {3, 1, 2};
  std::sort(arr, arr + 3);
  assert(arr[0] == 1);
}
