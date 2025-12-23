#include <assert.h>
#include <math.h>

int __signbitd(double);
int __signbitf(float);

int main()
{
  float f;
  double df = (double)f;
  __CPROVER_assert(
    isnan(f) || __signbitd(df) == __signbitf(f), "cast preserves sign");
  return 0;
}
