#include <assert.h>

void main()
{
  double a, b, c;
  __CPROVER_assume(a + b > c);
#ifdef EQUALITY
  double x = a, y = b, z = c;
  assert(!(z > x + y));
#else
  assert(!(c > a + b));
#endif
}
