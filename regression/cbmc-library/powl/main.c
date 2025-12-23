#include <assert.h>
#include <math.h>

int main()
{
  long double four = pow(2.0l, 2.0l);
  assert(four > 3.999l && four < 4.345l);
  return 0;
}
