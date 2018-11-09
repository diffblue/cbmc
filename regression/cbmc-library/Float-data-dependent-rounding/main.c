#include <assert.h>
#include <math.h>

#if defined(_MSC_VER) && _MSC_VER < 1800
// don't have fenv.h
#else
#include <fenv.h>
#endif

int main(void)
{
#if defined(_MSC_VER) && _MSC_VER < 1800
#else

#ifdef FE_UPWARD
#ifdef FW_DOWNWARD
  float f;
  float g;

  __CPROVER_assume(!isnan(f));
  __CPROVER_assume(!isnan(g));

  if(f > g)
  {
    fesetround(FE_UPWARD);
  }

  if(f < g)
  {
    fesetround(FE_DOWNWARD);
  }

  if((!isinf(f)) && (g > 0.0f))
  {
    float h = f + g;
    assert(h >= f);
  }
#endif
#endif

#endif

  return 1;
}
