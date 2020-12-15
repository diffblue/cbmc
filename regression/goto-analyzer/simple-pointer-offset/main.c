#include <assert.h>

int main()
{
  int a[2];

  int *p = &(a[0]);
  int *q = &(a[1]);
  int v = q - p;
  assert(v == 1);
}
