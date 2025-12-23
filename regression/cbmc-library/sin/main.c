#define _USE_MATH_DEFINES
#include <math.h>

int main()
{
  double s, f = 0.0, fStep = 0.1 * M_PI;
  int n = 0;

  do
  {
    s = sin(f);
    f += fStep;
    n++;
  } while(f < M_PI);

  assert(n < 11);
}
