#include <stdlib.h>

void foo(int *in1, int *in2, int **out1, int **out2)
  // clang-format off
  __CPROVER_assigns(*out1, *out2)
  __CPROVER_requires(
    __CPROVER_is_fresh(in1, sizeof(int)) &&
    __CPROVER_is_fresh(in2, sizeof(int)))
  __CPROVER_ensures(
    __CPROVER_is_fresh(*out1, sizeof(int)) &&
    __CPROVER_is_fresh(*out2, sizeof(int)))
// clang-format on
{
  __CPROVER_assert(__CPROVER_rw_ok(in1, sizeof(int)), "in1 is rw_ok");
  __CPROVER_assert(__CPROVER_rw_ok(in2, sizeof(int)), "in2 is rw_ok");
  __CPROVER_assert(
    !__CPROVER_same_object(in1, in2), "in1 and in2 do not alias");
  *out1 = malloc(sizeof(int));
  *out2 = malloc(sizeof(int));
}

int main()
{
  int *in1;
  int *in2;
  int *out1;
  int *out2;
  foo(in1, in2, &out1, &out2);
  return 0;
}
