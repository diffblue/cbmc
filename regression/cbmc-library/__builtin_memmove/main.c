#include <assert.h>
#include <string.h>

int main()
{
  int arr[] = {1, 2, 3, 4};
  // overlapping regions: a forward element-wise copy would give {1, 1, 1, 1}
  void *r = __builtin_memmove(arr + 1, arr, 3 * sizeof(int));
  assert(r == arr + 1);
  assert(arr[0] == 1);
  assert(arr[1] == 1);
  assert(arr[2] == 2);
  assert(arr[3] == 3);
  return 0;
}
