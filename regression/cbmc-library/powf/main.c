#include <assert.h>
#include <math.h>

int main()
{
  float four = powf(2.0f, 2.0f);
  assert(four > 3.999f && four < 4.345f);
  return 0;
}
