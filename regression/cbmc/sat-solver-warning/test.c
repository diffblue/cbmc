#include <assert.h>

int main()
{
  unsigned x = __VERIFIER_nondet_unsigned();
  unsigned y = x;
  x /= 2;
  y /= 2;
  assert(x == y);
  return 0;
}
