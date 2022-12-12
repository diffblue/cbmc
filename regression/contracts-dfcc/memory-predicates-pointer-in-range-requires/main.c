#include <assert.h>
#include <stdlib.h>

void foo(char *arr, size_t size, char *cur)
  // clang-format off
__CPROVER_requires(0 < size && __CPROVER_is_fresh(arr, size) &&
    __CPROVER_pointer_in_range_dfcc(arr, cur, arr + size))
__CPROVER_ensures(__CPROVER_pointer_in_range_dfcc(arr, cur, arr + size))
// clang-format on
{
  assert(__CPROVER_r_ok(arr, size));
  assert(__CPROVER_same_object(arr, cur));
  assert(arr <= cur && cur <= arr + size);
}

int main()
{
  char *arr;
  size_t size;
  char *cur;
  foo(arr, size, cur);
}
