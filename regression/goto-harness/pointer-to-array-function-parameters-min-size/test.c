#include <assert.h>

void min_array_size_test(int *arr, int sz)
{
  assert(sz > 2);
  for(int i = 0; i < sz; ++i)
  {
    arr[i] = i;
  }
  for(int i = 0; i < sz; ++i)
  {
    assert(arr[i] == i);
  }
}
