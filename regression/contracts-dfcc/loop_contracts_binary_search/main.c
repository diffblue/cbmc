#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>

#define NOT_FOUND (-1)

int binary_search(int val, int *buf, int size)
{
  if(size <= 0 || buf == NULL)
    return NOT_FOUND;

  int lb = 0, ub = size - 1;
  int mid = ((unsigned int)lb + (unsigned int)ub) >> 1;

  while(lb <= ub)
    // clang-format off
    __CPROVER_loop_invariant(0L <= lb && lb - 1L <= ub && ub < size)
    __CPROVER_loop_invariant(mid == ((unsigned int)lb + (unsigned int)ub) >> 1)
    __CPROVER_decreases(ub - lb)
    // clang-format on
    {
      if(buf[mid] == val)
        break;
      if(buf[mid] < val)
        lb = mid + 1;
      else
        ub = mid - 1;
      mid = ((unsigned int)lb + (unsigned int)ub) >> 1;
    }
  return lb > ub ? NOT_FOUND : mid;
}

int main()
{
  int val, size;
  int *buf = size >= 0 ? malloc(size * sizeof(int)) : NULL;

  int idx = binary_search(val, buf, size);
  if(idx != NOT_FOUND)
    assert(buf[idx] == val);
}
