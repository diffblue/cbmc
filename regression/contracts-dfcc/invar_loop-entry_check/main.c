#include <assert.h>
#include <stdlib.h>

typedef struct
{
  int *n;
} s;

void main()
{
  int *x1, y1, z1;
  x1 = &z1;

  while(y1 > 0)
    __CPROVER_loop_invariant(*x1 == __CPROVER_loop_entry(*x1))
    {
      --y1;
      *x1 = *x1 + 1;
      *x1 = *x1 - 1;
    }
  assert(*x1 == z1);

  int x2, y2, z2;
  x2 = z2;

  while(y2 > 0)
    __CPROVER_loop_invariant(x2 == __CPROVER_loop_entry(x2))
    {
      --y2;
      x2 = x2 + 1;
      x2 = x2 - 1;
    }
  assert(x2 == z2);

  int y3;
  s s0, s1, *s2 = &s0;
  s2->n = malloc(sizeof(int));
  s1.n = s2->n;

  while(y3 > 0)
    __CPROVER_loop_invariant(s2->n == __CPROVER_loop_entry(s2->n))
    {
      --y3;
      s0.n = s0.n + 1;
      s2->n = s2->n - 1;
    }

  assert(*(s1.n) == *(s2->n));
}
