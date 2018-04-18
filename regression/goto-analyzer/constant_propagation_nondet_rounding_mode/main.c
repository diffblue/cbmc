#include <assert.h>
#include <fenv.h>
#include <stdio.h>

int nondet_rounding_mode(void);

int main(void)
{
  // slightly bigger than 0.1
  float f = 1.0f / 10.0f;

  // now we don't know what rounding mode we're in
  __CPROVER_rounding_mode = nondet_rounding_mode();
  // depending on rounding mode 1.0f/10.0f could
  // be greater or smaller than 0.1

  // definitely not smaller than -0.1
  assert((1.0f / 10.0f) - f < -0.1f);
  // might be smaller than 0
  assert((1.0f / 10.0f) - f < 0.0f);
  // definitely smaller or equal to 0
  assert((1.0f / 10.0f) - f <= 0.0f);
  // might be greater or equal to 0
  assert((1.0f / 10.0f) - f >= 0.0f);
  // definitely not greater than 0
  assert((1.0f / 10.0f) - f > 0.0f);
}
