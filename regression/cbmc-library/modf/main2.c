#include <assert.h>
#include <math.h>

double nondet_double(void);

int main(void)
{
  double x = nondet_double();
  double ip;

  // C11 F.10.3.12: modf(+-inf, iptr) returns +-0 and stores +-inf
  if(isinf(x))
  {
    double r = modf(x, &ip);
    assert(!isnan(r));
    assert(r == 0.0);
  }

  // C11 7.12.6.12p2: both parts have the sign of the argument
  if(x == -3.0)
  {
    double r = modf(x, &ip);
    assert(signbit(r));
  }

  return 0;
}
