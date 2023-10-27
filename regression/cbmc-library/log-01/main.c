#include <assert.h>
#ifdef _WIN32
#  define _USE_MATH_DEFINES
#endif
#include <math.h>

int main()
{
  double one = log(M_E);
  assert(one > 0.942 && one < 1.002);
  return 0;
}
