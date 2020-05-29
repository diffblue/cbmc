#include <assert.h>

volatile int a;
volatile int b;

void main()
{
  assert(a == 0);

  assert(b == 0);
  assert(b != 0);
}
