#include <assert.h>

int main(void)
{
  __CPROVER_rounding_mode = 0;
  float rounded_up = 1.0f / 10.0f;
  __CPROVER_rounding_mode = 1;
  float rounded_down = 1.0f / 10.0f;
  assert(rounded_up - 0.1f >= 0);
  assert(rounded_down - 0.1f < 0);
  return 0;
}
