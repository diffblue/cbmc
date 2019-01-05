#include <limits.h>

int main()
{
  signed int x, y;

  // this is undefined in C11
  y = -1;
  x = INT_MIN % y;

  // always ok
  x = y % 2;
}
