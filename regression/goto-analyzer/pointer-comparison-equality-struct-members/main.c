#include <assert.h>

int main()
{
  struct int_pair
  {
    int a;
    int b;
  };
  struct int_pair x = {0, 1};

  int *pa = &(x.a);

  assert(pa == &(x.a));
  assert(pa != &(x.a));

  int *pb = &(x.b);
  assert(pb == &(x.a));
  assert(pb != &(x.a));

  struct int_pair y = {0, 1.0};
  assert(pa == &(y.a));
  assert(pa != &(y.a));

  int *pb = &(x.b);
  assert(pb == &(y.a));
  assert(pb != &(y.a));
}
