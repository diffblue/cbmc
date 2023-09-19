#include <assert.h>
#include <math.h>

int main()
{
  float e = expf(1.0f);
  assert(e > 2.713f && e < 2.886f);
  return 0;
}
