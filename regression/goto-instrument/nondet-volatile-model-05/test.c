#include <assert.h>

volatile int a;

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
  a;
}
