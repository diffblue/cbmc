#include <assert.h>
#include <stdlib.h>

typedef struct st1
{
  int data11;
  struct innert1
  {
    int inner_data11;
    int inner_data12;
  } inner1;
  int data12;
} st1_t;

typedef struct st2
{
  int data21;
  struct innert2
  {
    int inner_data21;
    int inner_data22;
  } inner2;
  int data22;
} st2_t;

st1_t dummy1 = {.data11 = 0,
                .inner1.inner_data11 = 0,
                .inner1.inner_data12 = 0,
                .data12 = 0};

st2_t dummy2 = {.data21 = 0,
                .inner2.inner_data21 = 0,
                .inner2.inner_data22 = 0,
                .data22 = 0};

void func(st1_t *p)
{
  assert(dummy1.data11 == 0); //should succeed
  assert(dummy1.inner1.inner_data11 == 0);
  assert(dummy1.inner1.inner_data12 == 0); //should fail
  assert(dummy1.data12 == 0);
  assert(dummy2.data21 == 0);              //should succeed
  assert(dummy2.inner2.inner_data21 == 0); //should fail
  assert(dummy2.inner2.inner_data22 == 0);
  assert(dummy2.data22 == 0);
}
