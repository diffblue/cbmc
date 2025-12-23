#include <assert.h>
#ifdef _WIN32
#  define _USE_MATH_DEFINES
#endif
#include <math.h>

int main()
{
  long double one = log2l(2.0l);
  assert(one > 0.999l && one < 1.087l);
  return 0;
}
