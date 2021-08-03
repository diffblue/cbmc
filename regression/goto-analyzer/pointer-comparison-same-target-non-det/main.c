#include <assert.h>

int main()
{
  int non_det;
  int a[5];

  int *p = &(a[0]);
  int *q = &(a[1]);
  int *r = non_det ? a + 1 : a + 2;

  assert(p == q);
  assert(p == r);
  assert(q == r);

  assert(p != q);
  assert(p != r);
  assert(q != r);

  assert(p < q);
  assert(p < r);
  assert(q < r);

  assert(p <= q);
  assert(p <= r);
  assert(q <= r);

  assert(p > q);
  assert(p > r);
  assert(q > r);

  assert(p >= q);
  assert(p >= r);
  assert(q >= r);
}
