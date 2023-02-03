#include <stdbool.h>
#include <stdlib.h>

bool my_contract(char *arr, size_t size, char *out)
  // clang-format off
__CPROVER_requires(__CPROVER_is_fresh(arr, size))
__CPROVER_requires(__CPROVER_is_fresh(out, sizeof(*out)))
__CPROVER_assigns((size > 0) : arr[0], *out)
__CPROVER_ensures(
    (size > 0) ==> __CPROVER_return_value &&
                   (arr[0] == 0) &&
                   (*out == __CPROVER_old(arr[0])))
__CPROVER_ensures(
    (size == 0) ==> !__CPROVER_return_value)
  // clang-format on
  ;

bool bar(char *arr, size_t size, char *out)
{
  if(size > 0)
  {
    *out = arr[0];
    arr[0] = 0;
    return true;
  }
  return false;
}

bool foo(char *arr, size_t size, char *out)
{
  return bar(arr, size, out);
}

void main()
{
  char *arr;
  size_t size;
  char *out;
  foo(arr, size, out);
}
