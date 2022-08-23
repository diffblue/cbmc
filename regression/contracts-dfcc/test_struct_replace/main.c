#include <assert.h>
#include <stdbool.h>

struct bar
{
  int baz;
  unsigned int qux;
};

// clang-format off
int foo(struct bar *x, struct bar *y)
  __CPROVER_assigns(*x, *y)
  __CPROVER_requires(
    __CPROVER_is_fresh(x, sizeof(struct bar)) &&
    __CPROVER_is_fresh(y, sizeof(struct bar)))
  __CPROVER_ensures(
    __CPROVER_return_value == (x->baz + x->qux) &&
    *x == *y)
// clang-format on
{
  x->baz = 5;
  x->qux = 5;
  *y = *x;
  return (x->baz + x->qux);
}

int main()
{
  struct bar *x = malloc(sizeof(*x));
  struct bar *y = malloc(sizeof(*y));
  int rval = foo(x, y);
  assert(rval == x->baz + x->qux);
  assert(*x == *y);
  return 0;
}
