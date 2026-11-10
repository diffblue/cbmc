#include <assert.h>
#include <string.h>

int main()
{
  int arr[] = {1, 2, 3, 4};
  __builtin_memmove(arr + 1, arr, 3 * sizeof(int));
  assert(arr[0] == 1);
  assert(arr[1] == 1);
  return 0;
}
