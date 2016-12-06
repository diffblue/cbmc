// Visual Studio needs to be 2013 onwards
#if defined(_MSC_VER) && !defined(__CYGWIN__) && _MSC_VER < 1800

// see http://www.johndcook.com/math_h.html

int main()
{
}

#else

#include <assert.h>
#include <fenv.h>

int main()
{
  #ifdef FE_DOWNWARD
  fesetround(FE_DOWNWARD);
  assert(fegetround()==FE_DOWNWARD);
  #endif

  #ifdef FE_TONEAREST
  fesetround(FE_TONEAREST);
  assert(fegetround()==FE_TONEAREST);
  #endif

  #ifdef FE_TOWARDZERO
  fesetround(FE_TOWARDZERO);
  assert(fegetround()==FE_TOWARDZERO);
  #endif

  #ifdef FE_UPWARD
  fesetround(FE_UPWARD);
  assert(fegetround()==FE_UPWARD);
  #endif
}

#endif
