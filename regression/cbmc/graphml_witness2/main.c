#include <stdlib.h>

extern void __VERIFIER_error();

static size_t one(size_t *foo)
{
  return *foo;
}

static size_t two(size_t *foo)
{
  return *foo;
}

size_t x = 0;

void step()
{
  x = one(0);
}

int main(void)
{
  while(1)
  {
    step();
    if(x == 0)
    {
      __VERIFIER_error();
    }
  }
  return 0;
}
