#include <stdlib.h>

void foo(int *a, int *b)
  // clang-format off
__CPROVER_requires(__CPROVER_is_fresh(a, 3*sizeof(int)))
__CPROVER_requires(__CPROVER_is_fresh(b, 3*sizeof(int)))
__CPROVER_assigns(__CPROVER_object_upto(a, 3*sizeof(int)))
__CPROVER_ensures(a[0] == b[0])
__CPROVER_ensures(a[1] == b[1])
__CPROVER_ensures(a[2] == b[2])
;

int nondet_int();

void bar()
{
  int a[6];
  int b[3];
  // c is either either a slice of `a` that overlaps a[0..2] or `b`
  int *c = nondet_int() ? &a[0] + 2: &b[0];
  int old_c0 = c[0];
  int old_c1 = c[1];
  int old_c2 = c[2];
  foo(a, c); // failure of preconditions
  __CPROVER_assert(a[0] == c[0], "same value 0");
  __CPROVER_assert(a[1] == c[1], "same value 1");
  __CPROVER_assert(a[2] == c[2], "same value 2");
  __CPROVER_assert(old_c0 == c[0], "unmodified 0");
  __CPROVER_assert(old_c1 == c[1], "unmodified 1");
  __CPROVER_assert(old_c2 == c[2], "unmodified 2");
}

int main()
{
  bar();
}
