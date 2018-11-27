#include <assert.h>
#include <stdlib.h>

typedef struct st
{
  struct st *next;
  struct st *prev;
  int data;
} st_t;

st_t dummy;

void func(st_t *p)
{
  assert(p != NULL);
  assert(p != &dummy);

  assert(p->prev != NULL);
  assert(p->prev != &dummy);

  assert(p->next != NULL);
  assert(p->next != &dummy);

  assert(p->prev->prev == NULL);
  assert(p->prev->next == NULL);
  assert(p->next->prev == NULL);
  assert(p->next->next == NULL);
}
