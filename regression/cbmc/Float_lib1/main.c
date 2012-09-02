#include <math.h>
#include <float.h>

#ifdef _WIN32
// see http://www.johndcook.com/math_h.html
#define fpclassify _fpclass
#endif

int main() {
  double xxx;

  assert(fpclassify(DBL_MAX+DBL_MAX)==FP_INFINITE);
  assert(fpclassify(0*(DBL_MAX+DBL_MAX))==FP_NAN);
  assert(fpclassify(1)==FP_NORMAL);
  assert(fpclassify(DBL_MIN)==FP_NORMAL);
  assert(fpclassify(DBL_MIN/2)==FP_SUBNORMAL);
  assert(fpclassify(-0.0)==FP_ZERO);

  assert(signbit(-1.0)!=0);
  assert(signbit(1.0)==0);
}
