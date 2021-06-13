#include <assert.h>
#include <stdlib.h>

static int add_operator(const int *a, const int *b)
{
  return (*a + *b);
}

// clang-format off
int foo(int *x, int *y)
  __CPROVER_requires(x != NULL)
  __CPROVER_requires(y != NULL)
  __CPROVER_ensures(__CPROVER_return_value == 10)
// clang-format on
{
  int (*sum)(const int *, const int *) = add_operator;
  return sum(x, y);
}

int main()
{
  int x = 5;
  int y = 5;
  assert(foo(&x, &y) == 10);
  return 0;
}
