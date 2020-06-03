#include <assert.h>

volatile int a;
volatile int b;
volatile int c;

int model()
{
  int value;
  __CPROVER_assume(value >= 0);
  return value;
}

void main()
{
  assert(a == 0);

  assert(b >= 0);
  assert(b == 0);
  assert(b != 0);

  assert(c >= 0);
  assert(c == 0);
  assert(c != 0);
}
