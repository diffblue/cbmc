#include <assert.h>
#include <math.h>
#include <fenv.h>

int main (void) {
  float f;
  float g;

  __CPROVER_assume(!isnan(f));
  __CPROVER_assume(!isnan(g));

  if (f > g) {
    fesetround(FE_UPWARD);
  }

  if (f < g) {
    fesetround(FE_DOWNWARD);
  }

  if ((!isinf(f)) && (g > 0.0f)) {
    float h = f + g;
    assert(h >= f);
  }

  return 1;
}
