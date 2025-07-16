#include <assert.h>

void test_fn(int *a)
  // clang-format off
  __CPROVER_requires((a == (int*)0) || __CPROVER_is_fresh(a, sizeof(*a)))
  __CPROVER_requires((a != (int*)0) ==> (*a != 5))
  __CPROVER_ensures((a != (int*)0) ==> (*a == 5))
  __CPROVER_assigns(*a)
// clang-format on
{
  assert((a == (int *)0) || (*a != 5));
  if(a != (int *)0)
  {
    *a = 5;
  }
}
