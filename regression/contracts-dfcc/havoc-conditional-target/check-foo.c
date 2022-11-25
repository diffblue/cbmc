#include <stdlib.h>

void foo(int *out)
  // clang-format off
__CPROVER_requires(out ==> __CPROVER_is_fresh(out, sizeof(*out)))
__CPROVER_assigns(out: *out)
__CPROVER_ensures(out ==> *out == 1)
// clang-format on
{
  if(out)
    *out = 1;
}

int nondet_int();

void main()
{
  int *out;
  foo(out);
}
