#include <assert.h>
#include <stdbool.h>

struct bar
{
  int baz;
  unsigned int qux;
};

// clang-format off
int foo(struct bar *x)
  __CPROVER_assigns(*x)
  __CPROVER_requires(
    __CPROVER_is_fresh(x, sizeof(struct bar)))
  __CPROVER_ensures(
    __CPROVER_return_value == (x->baz + x->qux))
// clang-format on
{
  x->baz = 5;
  x->qux = 5;
  return (x->baz + x->qux);
}

int main()
{
  struct bar *x;
  int rval = foo(x);
  assert(rval == 10);
  return 0;
}
