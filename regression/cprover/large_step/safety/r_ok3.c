#include <stdlib.h>

int main()
{
  int x;
  int *p = malloc(sizeof(int));

  __CPROVER_assert(__CPROVER_r_ok(&x), "&x ok to read");
  __CPROVER_assert(__CPROVER_r_ok("foo", 4), "string literal ok to read");
  __CPROVER_assert(__CPROVER_r_ok(p), "p ok to read");

  return 0;
}
