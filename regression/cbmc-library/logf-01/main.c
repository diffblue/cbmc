#include <assert.h>
#ifdef _WIN32
#  define _USE_MATH_DEFINES
#endif
#include <math.h>

int main()
{
  float one = logf(M_E);
  assert(one > 0.942f && one < 1.002f);
  return 0;
}
