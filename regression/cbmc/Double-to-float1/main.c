#include <assert.h>
#include <math.h>

float nondet_float();

int main()
{
  float f=nondet_float();

  double d = (double)f;
  float ff = (float)d;

  assert((f == ff) || (isnan(f) && isnan(ff)));
}
