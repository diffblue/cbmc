#include <assert.h>
#include <math.h>

int main()
{
  double four = pow(2.0, 2.0);
  assert(four > 3.999 && four < 4.345);
  return 0;
}
