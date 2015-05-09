#include <assert.h>
#include <math.h>

#ifdef _MSC_VER
#include <float.h>
int isnanf(float);
#else
#include <fenv.h>
#endif

int main (void) {
  float f;
  float g;

  __CPROVER_assume(!isnan(f));
  __CPROVER_assume(!isnan(g));

  if (f > g) {
    #ifdef _MSC_VER
    _controlfp(_RC_UP, _MCW_RC);
    #else
    fesetround(FE_UPWARD);
    #endif
  }

  if (f < g) {
    #ifdef _MSC_VER
    _controlfp(_RC_DOWN, _MCW_RC);
    #else
    fesetround(FE_DOWNWARD);
    #endif
  }

  if ((!isinf(f)) && (g > 0.0f)) {
    float h = f + g;
    assert(h >= f);
  }

  return 1;
}
