#include <assert.h>
#include <math.h>

double nondet_double(void);

int main(void)
{
  double x = nondet_double();
  if(isnan(x))
  {
    double r = fdim(x, 1.0);
    // C11 F.10p11: NaN argument returns NaN
    assert(isnan(r));
  }
  return 0;
}
