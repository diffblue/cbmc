#include <assert.h>
#include <stdlib.h>

struct A
{
  struct A *p;
};

int main(void)
{
  struct A x = {&x};
  struct A *r = x.p->p = NULL;
  assert(r == NULL);

  struct A arr[2] = {arr, 0};
  r = arr[0].p->p += 1;
  assert(r == &arr[1]);
}
