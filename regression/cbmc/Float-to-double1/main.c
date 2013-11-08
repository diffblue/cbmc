#include <assert.h>
#include <math.h>

#ifdef _WIN32
#include <float.h>
#define isnan _isnan
#endif

float nondet_float();

int main()
{
  float f=nondet_float();

  double d = (double)f;
  float ff = (float)d;

  assert((f == ff) || (isnan(f) && isnan(ff)));
}
