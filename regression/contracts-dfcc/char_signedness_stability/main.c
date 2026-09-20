#include <stdlib.h>
#include <string.h>

int x;

void foo(int *p) __CPROVER_requires(__CPROVER_is_fresh(p, sizeof(int)))
  __CPROVER_assigns(*p, x) __CPROVER_ensures(*p == 42)
{
  *p = 42;
  x = 1;
}

int main()
{
  int a[4], b[4];
  memset(a, 0, sizeof(a));
  memcpy(b, a, sizeof(a));
  memmove(a, b, sizeof(a));
  __CPROVER_havoc_slice(a, 2 * sizeof(int));

  int *q = malloc(sizeof(int));
  if(q)
    foo(q);
  return 0;
}
