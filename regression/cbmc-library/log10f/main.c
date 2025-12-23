#include <assert.h>
#ifdef _WIN32
#  define _USE_MATH_DEFINES
#endif
#include <math.h>

int main()
{
  float one = log10f(10.0f);
  assert(one > 0.978f && one < 1.005f);
  return 0;
}
