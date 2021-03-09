#include <assert.h>

int main()
{
  int a[2];
  int b[2];

  int *p = a;
  int *q = a;

  assert(p - q == 0);

  q = b;
  assert(p - q == 0);
}
