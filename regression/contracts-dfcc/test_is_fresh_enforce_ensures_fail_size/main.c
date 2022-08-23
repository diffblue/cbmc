#include <stdlib.h>

#define SIZE 10
int nondet_int();

void foo(char **out)
  // clang-format off
  __CPROVER_assigns(*out)
  __CPROVER_ensures(__CPROVER_is_fresh(*out, SIZE))
// clang-format on
{
  *out = malloc(nondet_int() ? SIZE : SIZE - 1);
}

int main()
{
  char *out;
  foo(&out);
  return 0;
}
