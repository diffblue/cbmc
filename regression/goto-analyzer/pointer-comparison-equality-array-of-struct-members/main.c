#include <assert.h>

int main()
{
  struct int_pair
  {
    int a;
    int b;
  };
  struct int_pair x[2];

  int *pa = &(x[0].a);

  assert(pa == &(x[0].a));
  assert(pa != &(x[0].a));
  assert(pa == &(x[0].b));
  assert(pa != &(x[0].b));
  assert(pa == &(x[1].a));
  assert(pa != &(x[1].a));
  assert(pa == &(x[1].b));
  assert(pa != &(x[1].b));
}
