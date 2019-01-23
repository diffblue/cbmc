#include <assert.h>
#include <stdlib.h>

typedef struct st
{
  struct st *next;
  int data;
} st_t;

st_t dummy;

st_t *func();

void main()
{
  st_t *st = func();

  assert(st != NULL);

  assert(st->next != NULL);
  assert(st->next->next != NULL);
  assert(st->next->next->next == NULL);

  assert(st != &dummy);
  assert(st->next != &dummy);
  assert(st->next->next != &dummy);
}
