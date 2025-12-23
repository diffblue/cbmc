#include <assert.h>
#include <math.h>

long double __builtin_powil(long double, int);

int main()
{
  long double four = __builtin_powil(2.0l, 2);
  assert(four > 3.999l && four < 4.345l);
  return 0;
}
