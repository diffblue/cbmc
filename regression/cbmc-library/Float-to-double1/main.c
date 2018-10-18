#include <assert.h>
#include <math.h>

#if defined(_WIN32) && !defined(__CYGWIN__)
#include <float.h>
#define isnan _isnan
#endif

float nondet_float();

int main()
{
  float f = nondet_float();

  double d = (double)f;
  float ff = (float)d;

  assert((f == ff) || (isnan(f) && isnan(ff)));
}
