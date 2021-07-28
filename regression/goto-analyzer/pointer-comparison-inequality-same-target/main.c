#include <assert.h>

int main()
{
  int a[2];

  int *p = &(a[0]);
  int *q = &(a[1]);

  assert(p <= a);
  assert(p < a);
  assert(p >= a);
  assert(p > a);

  assert(p <= q);
  assert(p < q);
  assert(p >= q);
  assert(p > q);

  assert(q <= p);
  assert(q < p);
  assert(q >= p);
  assert(q > p);
}
