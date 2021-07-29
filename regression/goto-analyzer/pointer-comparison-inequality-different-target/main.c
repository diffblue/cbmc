#include <assert.h>

int main()
{
  int a[2];
  int b[2];

  int *p = &(a[0]);
  int *q = &(b[1]);

  // p and q point to different base objects so these
  // comparisons are undefined. Consequently we evaluate
  // them as UNKNOWN
  assert(p <= q);
  assert(p < q);
  assert(p >= q);
  assert(p > q);

  assert(q <= p);
  assert(q < p);
  assert(q >= p);
  assert(q > p);
}
