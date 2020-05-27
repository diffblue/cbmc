#include <assert.h>

void main()
{
  int a[2] = {0};

  volatile int i = 0;
  a[i] = 1;

  assert(a[1] == 0); // should fail
}
