#include <assert.h>

int g = 1;

void harness()
{
  for(int i = 0; i < 4; ++i)
  {
    int* x;
    x = &g;
    assert(*x == 1);
  }
}
