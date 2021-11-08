#include <assert.h>
#include <stdlib.h>

void foo(char *p, char *q)
{
  if(p)
    free(p);
  if(q)
    free(q);
}

_Bool nondet_bool();

int main()
{
  char *p = nondet_bool() ? NULL : malloc(10);
  char *q = nondet_bool() ? NULL : malloc(12);
  foo(p, q);
  // no valid objects live at p or q anymore
  assert(!__CPROVER_r_ok(p, 0) & !__CPROVER_r_ok(q, 0));
}
