#include <assert.h>
#include <stdlib.h>

typedef struct st1
{
  struct st2 *to_st2;
  int data;
} st1_t;

typedef struct st2
{
  struct st1 *to_st1;
  int data;
} st2_t;

st1_t dummy1;
st2_t dummy2;

void func(st1_t *p)
{
  assert(p != NULL);
  assert(p->to_st2 != NULL);
  assert(p->to_st2->to_st1 != NULL);
  assert(p->to_st2->to_st1->to_st2 == NULL);

  assert(p != &dummy1);
  assert(p->to_st2 != &dummy2);
  assert(p->to_st2->to_st1 != &dummy1);
}
