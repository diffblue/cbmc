#include <assert.h>
#include <math.h>

float nondet_float(void);

int main(void)
{
  // symbolic argument: the square root is computed by the solver
  float f = nondet_float();
  __CPROVER_assume(f == 2.0f);
  assert(sqrtf(f) == 0x1.6a09e6p+0f);
  return 0;
}
