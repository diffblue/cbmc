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

  int y1_bak = y1;
  while(y1 > 0)
    // clang-format off
    __CPROVER_loop_invariant(
      *x1 == __CPROVER_loop_old(*x1) + 1
      &&
      __CPROVER_loop_entry(*x1) <= *x1 <= __CPROVER_loop_entry(*x1) + __CPROVER_loop_entry(y1)
    )
    // clang-format on
    {
      --y1;
      *x1 = *x1 + 1;
    }
  assert(*x1 == z1 + y1_bak);

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

  int y2_bak = y2;
  while(y2 > 0)
    // clang-format off
    __CPROVER_loop_invariant(
      *x2 == __CPROVER_loop_old(*x2) + 1
      &&
      __CPROVER_loop_entry(*x2) <= *x2 <= __CPROVER_loop_entry(*x2) + __CPROVER_loop_entry(y2)
    )
    // clang-format on
    {
      --y2;
      x2 = x2 + 1;
      x2 = x2 - 1;
    }
  assert(x2 == z2);

  int y3;
  s *s1, *s2;
  s2->n = malloc(sizeof(int));
  s1->n = s2->n;

  while(y3 > 0)
    __CPROVER_loop_invariant(s1->n == __CPROVER_loop_entry(s1->n))
    {
      --y3;
      s1->n = s1->n + 1;
      s1->n = s1->n - 1;
    }
  assert(*(s1->n) == *(s2->n));

  int y3_bak = y3;
  while(y3 > 0)
    // clang-format off
    __CPROVER_loop_invariant(
      *(s1->n) == __CPROVER_loop_old(*(s1->n)) + 1
      &&
      __CPROVER_loop_entry(*(s->n)) <= *(s->n) <= __CPROVER_loop_entry(*(s->n)) + __CPROVER_loop_entry(y3)
    )
    // clang-format on
    {
      --y3;
      *(s1->n) = *(s1->n) + 1;
    }
  assert(*(s1->n) == *(s2->n) + y3_bak);
}
