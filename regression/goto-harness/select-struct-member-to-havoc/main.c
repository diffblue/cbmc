#include <assert.h>
#include <stdlib.h>

typedef struct st
{
  int data1;
  struct innert
  {
    int inner_data1;
    int inner_data2;
  } inner;
  int data2;
} st_t;

st_t dummy = {.data1 = 0,
              .inner.inner_data1 = 0,
              .inner.inner_data2 = 0,
              .data2 = 0};

void func(st_t *p)
{
  assert(dummy.data1 == 0); //should succeed
  assert(dummy.inner.inner_data1 == 0);
  assert(dummy.inner.inner_data2 == 0); //should fail
  assert(dummy.data2 == 0);
}
