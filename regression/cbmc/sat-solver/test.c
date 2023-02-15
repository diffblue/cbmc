#include <assert.h>

int main()
{
  unsigned x;
  unsigned y = x / 2;
  assert(y != x);
  assert(y <= x);
  return 0;
}
