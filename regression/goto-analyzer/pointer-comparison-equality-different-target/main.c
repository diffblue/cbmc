#include <assert.h>

int main()
{
  int a[2];
  int b[2];
  int c;

  int *p = &(a[0]);
  int *q = &(b[1]);
  int *r = &c;

  assert(p == q);
  assert(p == r);
  assert(q == r);

  assert(p != q);
  assert(p != r);
  assert(q != r);
}
