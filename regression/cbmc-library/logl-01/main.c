#include <assert.h>
#ifdef _WIN32
#  define _USE_MATH_DEFINES
#endif
#include <math.h>

int main()
{
  long double one = logl(M_E);
  assert(one > 0.942l && one < 1.002l);
  return 0;
}
