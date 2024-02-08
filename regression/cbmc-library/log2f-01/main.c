#include <assert.h>
#ifdef _WIN32
#  define _USE_MATH_DEFINES
#endif
#include <math.h>

int main()
{
  float one = log2f(2.0f);
  assert(one > 0.999f && one < 1.087f);
  return 0;
}
