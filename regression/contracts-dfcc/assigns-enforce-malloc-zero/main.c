#include <stdbool.h>
#include <stdlib.h>

bool foo(char *a, size_t size, size_t *out)
  // clang-format off
  __CPROVER_requires(a == NULL || __CPROVER_is_fresh(a, size))
  __CPROVER_requires(__CPROVER_is_fresh(out, sizeof(*out)))
  __CPROVER_assigns(a: __CPROVER_object_from(a), *out)
  __CPROVER_ensures(
    a && __CPROVER_return_value ==>
      (0 <= *out && *out < size &&
      a[*out] == 0)
  )
// clang-format on
{
  size_t i;
  if(a && 0 <= i && i < size)
  {
    a[i] = 0;
    *out = i;
    return true;
  }
  return false;
}

void main()
{
  char *a;
  size_t size;
  size_t *out;
  foo(a, size, out);
}
