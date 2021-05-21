#include <stdlib.h>

typedef int (*fptr_t)(void);

void entry_point(fptr_t f, fptr_t f_but_may_be_null)
{
  __CPROVER_assert(
    f != (void *)0, "assertion f != (void *)0 - expected to succeed");
  __CPROVER_assert(
    f == (void *)0, "assertion f == (void *)0 - expected to fail");
  __CPROVER_assert(
    f_but_may_be_null != (void *)0,
    "assertion f_but_may_be_null != (void *)0 - expected to fail");
  __CPROVER_assert(
    f_but_may_be_null == (void *)0,
    "assertion f_but_may_be_null == (void *)0 - expected to fail");
  __CPROVER_assert(
    f_but_may_be_null == (void *)0 || f() == f_but_may_be_null(),
    "assertion f_but_may_be_null == (void *)0 || f() == f_but_may_be_null()");
}

int f(void)
{
  return 42;
}
