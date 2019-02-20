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

typedef struct st3
{
  st1_t *array[3];
} st3_t;

st1_t dummy1;
st2_t dummy2;

void func(st3_t *p)
{
  assert(p != NULL);
  for(int index = 0; index < 3; index++)
  {
    assert(p->array[index]->to_st2 != NULL);
    assert(p->array[index]->to_st2->to_st1 != NULL);
    assert(p->array[index]->to_st2->to_st1->to_st2 == NULL);
  }

  assert(p->array[0] != p->array[1]);
  assert(p->array[1] != p->array[2]);
  assert(p->array[0] != p->array[2]);
}
