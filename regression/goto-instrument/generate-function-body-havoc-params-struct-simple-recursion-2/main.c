#include <assert.h>
#include <stdlib.h>

typedef struct st
{
  struct st *next;
  struct st *prev;
  int data;
} st_t;

st_t dummy;

void func(st_t *p);

void main()
{
  st_t st;

  func(&st);

  assert(st.prev != NULL);
  assert(st.prev != &dummy);

  assert(st.next != NULL);
  assert(st.next != &dummy);

  assert(st.prev->prev == NULL);
  assert(st.prev->next == NULL);
  assert(st.next->prev == NULL);
  assert(st.next->next == NULL);
}
