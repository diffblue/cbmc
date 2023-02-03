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

void bar()
{
  int i = 0;
  int *out = nondet_int() ? &i : NULL;
  foo(out);
  // clang-format off
  __CPROVER_assert(!out ==> (i == 0), "out not null implies initial value");
  __CPROVER_assert(out ==> (i == 1), "out null implies updated value");
  // clang-format on
}

int main(void)
{
  bar();
}
