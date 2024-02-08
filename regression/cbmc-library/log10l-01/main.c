#include <assert.h>
#ifdef _WIN32
#  define _USE_MATH_DEFINES
#endif
#include <math.h>

int main()
{
  long double one = log10l(10.0l);
  assert(one > 0.978l && one < 1.005l);
  return 0;
}
