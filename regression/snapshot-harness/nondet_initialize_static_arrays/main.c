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

st3_t *p;

void initialize()
{
  p = malloc(sizeof(st3_t));
}

void checkpoint()
{
}

int main()
{
  initialize();
  checkpoint();

  assert(p != NULL);
  for(int index = 0; index < 3; index++)
  {
    // check that the arrays in structs (and structs in those arrays) were
    // initialized up-to the input depth
    assert(p->array[index]->to_st2 != NULL);
    assert(p->array[index]->to_st2->to_st1 != NULL);
    assert(p->array[index]->to_st2->to_st1->to_st2 == NULL);
  }

  // non-deterministically initializated objects should not be equal
  assert(p->array[0] != p->array[1]);
  assert(p->array[1] != p->array[2]);
  assert(p->array[0] != p->array[2]);
}
