#include <assert.h>
#include <stdlib.h>

typedef struct st
{
  struct st *next;
  int data;
} st_t;

st_t dummy;

void func(st_t *p)
{
  assert(p != NULL);
  assert(p->next != NULL);
  assert(p->next->next != NULL);
  assert(p->next->next->next == NULL);

  assert(p != &dummy);
  assert(p->next != &dummy);
  assert(p->next->next != &dummy);
}
