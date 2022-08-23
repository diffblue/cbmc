#include <stdbool.h>
#include <stdlib.h>

char nondet_char();

char *foo(char *a, char *b, size_t s)
  // clang-format off
__CPROVER_requires(s > 0)
__CPROVER_requires(__CPROVER_is_fresh(a, s))
__CPROVER_requires(__CPROVER_is_fresh(b, s))
__CPROVER_assigns(a[0])
__CPROVER_ensures(__CPROVER_is_fresh(__CPROVER_return_value, s))
// clang-format on
{
  a[0] = nondet_char();
  return malloc(s);
}

char *bar(char *a, char *b, size_t s)
{
  return foo(a, b, s);
}

int main()
{
  size_t s;
  __CPROVER_assume(0 < s && s < __CPROVER_max_malloc_size);
  char *a = malloc(s);
  char *b = malloc(s);

  char *c = bar(a, b, s);
  __CPROVER_assert(__CPROVER_rw_ok(c, s), "c is rw_ok");
  __CPROVER_assert(c != a, "c and a are distinct");
  __CPROVER_assert(c != b, "c and b are distinct");

  char *d = bar(a, b, s);
  __CPROVER_assert(__CPROVER_rw_ok(d, s), "d is rw_ok");
  __CPROVER_assert(d != a, "d and a are distinct");
  __CPROVER_assert(d != b, "d and b are distinct");
  __CPROVER_assert(d != c, "d and c distinct");

  return 0;
}
