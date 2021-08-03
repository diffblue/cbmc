#include <assert.h>

int main()
{
  int a[2];
  int *p = a;

  ++p;
  assert(p == &(a[1]));

  --p;
  assert(p == a);
}
