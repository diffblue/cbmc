#include <assert.h>
#ifdef _WIN32
#  define _USE_MATH_DEFINES
#endif
#include <math.h>

int main()
{
  double one = log2(2.0);
  assert(one > 0.999 && one < 1.087);
  return 0;
}
