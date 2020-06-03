#include <assert.h>

volatile int a;
volatile int b;

int model_a()
{
  return 1;
}

int model_b()
{
  return 2;
}

void main()
{
  int result = a + b;
  assert(result == 3);
}
