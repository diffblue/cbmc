#include <assert.h>
#include <stdlib.h>

int get_at_idx(int const *const arr, const size_t len, const size_t idx)
  __CPROVER_requires(__CPROVER_r_ok(arr, len) && idx < len)
    __CPROVER_ensures(__CPROVER_return_value == arr[idx])
{
  return arr[idx];
}

void main()
{
  int a[5] = {0};
  a[3] = 7;
  int x = get_at_idx(a, 5, 3);
  assert(x == 7);
}
