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

int nondet_int();

void bar(int size)
{
  size_t out;
  char *a = malloc(size);
  bool res = foo(a, size, &out);
  if(a && res)
    __CPROVER_assert(a[out] == 0, "expecting SUCCESS");
}

void main()
{
  size_t size;
  bar(size);
}
