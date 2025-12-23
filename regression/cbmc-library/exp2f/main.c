#include <assert.h>
#include <math.h>

int main()
{
  float two = exp2f(1.0f);
  assert(two > 1.999f && two < 2.001f);
  return 0;
}
