#include <limits.h>

int main()
{
  signed int x, y;

  x = INT_MIN;

  // this is an overflow
  y = -x;

  // ok
  x = -(x + 1);

  unsigned a, b;

  a = 1;
  a = -a; // overflow, -1 is not representable

  b = 0;
  b = -b; // ok
}
