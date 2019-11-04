#include <assert.h>
#include <stdlib.h>

typedef struct st
{
  struct st *next;
  int data;
} st_t;

void func(st_t *p, st_t *q)
{
  assert(p != NULL);
  assert(p->next != NULL);

  assert(p == q);
}
