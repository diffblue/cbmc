#include <assert.h>

int main(void)
{
  float f   = -0x1.0p-127f;
  double d  = -0x1.0p-127;
  double fp = (double)f;

  assert(d == fp);

  return 0;
}
