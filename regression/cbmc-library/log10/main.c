#include <assert.h>
#ifdef _WIN32
#  define _USE_MATH_DEFINES
#endif
#include <math.h>

int main()
{
  double one = log10(10.0);
  assert(one > 0.978 && one < 1.005);
  return 0;
}
