#include <assert.h>
void test(int *arr, int sz)
{
  assert(sz < 10);
  for(int i = 0; i < sz; ++i)
  {
    arr[i] = 0;
  }
}
