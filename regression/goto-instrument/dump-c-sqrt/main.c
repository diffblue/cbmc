#include <assert.h>
#include <math.h>

int main(void)
{
  float x = 4.0f;
  assert(sqrtf(x) == 2.0f);

  long double y = 4.0L;
  assert(sqrtl(y) == 2.0L);

  return 0;
}
