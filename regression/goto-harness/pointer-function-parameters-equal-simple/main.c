#include <assert.h>
#include <stdlib.h>

typedef struct st1
{
  struct st *next;
  int data;
} st1_t;

typedef struct st2
{
  struct st *next;
  int data;
} st2_t;

void func(st1_t *p, st1_t *q, st2_t *r, st2_t *s, st2_t *t)
{
  assert(p != NULL);
  assert(p->next != NULL);

  assert(p == q);

  assert((void *)p != (void *)r);

  assert(r == s);
  assert(r == t);
}
