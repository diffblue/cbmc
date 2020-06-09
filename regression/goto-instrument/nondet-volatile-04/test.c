#include <assert.h>

volatile int x;
int y;

void main()
{
  y = x;
  assert(x == y);
}
