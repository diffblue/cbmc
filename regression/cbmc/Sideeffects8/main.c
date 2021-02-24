#include <assert.h>
#include <stdlib.h>

struct A
{
  struct A *p;
};

struct A *return_null()
{
  return NULL;
}

int main(void)
{
  struct A x = {&x};
  struct A *r = x.p->p = NULL;
  assert(r == NULL);

  struct A x2 = {&x2};
  r = x2.p->p = return_null();
  assert(r == NULL);

  struct A arr[2] = {arr, 0};
  r = arr[0].p->p += 1;
  assert(r == &arr[1]);

  struct A arr2[2] = {arr2, 0};
  r = ++(arr2[0].p->p);
  assert(r == &arr2[1]);

  struct A arr3[2] = {arr3, 0};
  r = (arr3[0].p->p)++;
  assert(r == &arr3[0]);
}
