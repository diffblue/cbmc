#include <assert.h>
#include <math.h>

double __builtin_powi(double, int);

int main()
{
  double four = __builtin_powi(2.0, 2);
  assert(four > 3.999 && four < 4.345);
  return 0;
}
