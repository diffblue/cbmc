#include <assert.h>
#include <stdlib.h>

typedef struct st
{
  struct st *next;
  int data;
} st_t;

st_t dummy;

void func(st_t *p);

void main()
{
  st_t st;

  func(&st);

  assert(st.next != NULL);
  assert(st.next->next != NULL);
  assert(st.next->next->next == NULL);

  assert(st.next != &dummy);
  assert(st.next->next != &dummy);
}
