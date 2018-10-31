#include <assert.h>
#include <stdlib.h>

typedef struct st
{
  int data;
} st_t;

st_t dummy;

void func(st_t *p)
{
  assert(p != NULL);
  assert(p != &dummy);
  assert(p->data >= 4854549);
  assert(p->data < 4854549);
}
