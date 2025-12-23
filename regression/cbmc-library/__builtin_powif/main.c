#include <assert.h>
#include <math.h>

float __builtin_powif(float, int);

int main()
{
  float four = __builtin_powif(2.0f, 2);
  assert(four > 3.999f && four < 4.345f);
  return 0;
}
