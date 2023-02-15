#include <assert.h>

int main()
{
  unsigned x;
  unsigned y = x;
  x /= 2;
  y /= 2;
  assert(x == y);
  return 0;
}
