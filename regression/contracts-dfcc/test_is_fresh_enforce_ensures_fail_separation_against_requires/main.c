#include <stdlib.h>

#define SIZE 10
int nondet_int();
void foo(char *in1, char *in2, char **out)
  // clang-format off
  __CPROVER_assigns(*out)
  __CPROVER_requires(
    __CPROVER_is_fresh(in1, SIZE) &&
    __CPROVER_is_fresh(in2, SIZE))
  __CPROVER_ensures(
    __CPROVER_is_fresh(*out, SIZE))
// clang-format on
{
  __CPROVER_assert(__CPROVER_rw_ok(in1, SIZE), "in1 is rw_ok");
  __CPROVER_assert(__CPROVER_rw_ok(in2, SIZE), "in2 is rw_ok");
  __CPROVER_assert(
    !__CPROVER_same_object(in1, in2), "in1 and in2 do not alias");
  // nondeterministically fresh or aliased
  *out = nondet_int() ? malloc(SIZE) : in1;
}

int main()
{
  char *in1;
  char *in2;
  char *out;
  foo(in1, in2, &out);
  return 0;
}
