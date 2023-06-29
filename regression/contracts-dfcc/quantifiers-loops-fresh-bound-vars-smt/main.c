#include <stdlib.h>
void foo(char *dst, const char *src, size_t n)
  // clang-format off
  __CPROVER_requires(__CPROVER_is_fresh(src, n))
  __CPROVER_requires(__CPROVER_is_fresh(dst, n))
  __CPROVER_assigns(__CPROVER_object_from(dst))
  __CPROVER_ensures(__CPROVER_forall {
    size_t j;
    j < n ==> dst[j] == src[j]
  })
// clang-format on
{
  for(size_t i = 0; i < n; i++)
    // clang-format off
    __CPROVER_assigns(i, __CPROVER_object_from(dst))
    __CPROVER_loop_invariant(i <= n)
    __CPROVER_loop_invariant(
      __CPROVER_forall { size_t j; j < i ==> dst[j] == src[j] })
    // clang-format on
    {
      dst[i] = src[i];
    }
}

int main()
{
  char *dst;
  char *src;
  size_t n;
  foo(dst, src, n);
  return 0;
}
