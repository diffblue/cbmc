#include <stdlib.h>

void bar(int **x) __CPROVER_assigns(*x)
  __CPROVER_requires(__CPROVER_is_fresh(x, sizeof(*x)))
    __CPROVER_ensures(__CPROVER_is_fresh(*x, sizeof(**x)))
{
  __CPROVER_assert(__CPROVER_r_ok(x, sizeof(*x)), "x is r_ok");
  *x = malloc(sizeof(**x));
  __CPROVER_assert(__CPROVER_r_ok(*x, sizeof(**x)), "deref x is r_ok");
}

void foo(int *x1, int **x2) __CPROVER_assigns(*x2)
  __CPROVER_requires(__CPROVER_is_fresh(x1, sizeof(*x1)))
    __CPROVER_requires(__CPROVER_is_fresh(x2, sizeof(*x2)))
      __CPROVER_requires(__CPROVER_is_fresh(*x2, sizeof(**x2)))
        __CPROVER_ensures(__CPROVER_is_fresh(*x2, sizeof(**x2)))
{
  __CPROVER_assert(__CPROVER_r_ok(x1, sizeof(*x1)), "x1 r_ok");
  __CPROVER_assert(__CPROVER_r_ok(x2, sizeof(*x2)), "x2 r_ok");
  __CPROVER_assert(__CPROVER_r_ok(*x2, sizeof(**x2)), "deref x2 r_ok");
  int *old_x2 = *x2;
  bar(x2);
  __CPROVER_assert(__CPROVER_r_ok(*x2, sizeof(**x2)), "deref x2 r_ok");
  __CPROVER_assert(!__CPROVER_same_object(*x2, old_x2), "x2 updated");
}
