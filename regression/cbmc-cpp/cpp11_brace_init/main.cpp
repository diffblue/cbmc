#include <cassert>

int main()
{
  int arr[] = {1, 2, 3};
  assert(arr[0] == 1);
  assert(arr[2] == 3);

  int x{42};
  assert(x == 42);

  return 0;
}
