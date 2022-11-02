#include <stdlib.h>

#define SIZE 10
int nondet_int();

void foo(char **out1, char **out2)
  // clang-format off
  __CPROVER_assigns(*out1, *out2)
  __CPROVER_ensures(__CPROVER_is_fresh(*out1, SIZE))
  __CPROVER_ensures(__CPROVER_is_fresh(*out2, SIZE))
// clang-format on
{
  *out1 = malloc(SIZE);
  *out2 = nondet_int() ? malloc(SIZE) : *out1;
}

int main()
{
  char *out1;
  char *out2;
  foo(&out1, &out2);
  return 0;
}
