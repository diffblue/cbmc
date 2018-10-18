// This is C99, but currently only works with clang.
// gcc and Visual Studio appear to hard-wire FLT_ROUNDS to 1.

#ifdef __clang__

#include <assert.h>
#include <fenv.h>
#include <float.h>

int main()
{
  fesetround(FE_DOWNWARD);
  assert(FLT_ROUNDS==3);

  fesetround(FE_TONEAREST);
  assert(FLT_ROUNDS==1);

  fesetround(FE_TOWARDZERO);
  assert(FLT_ROUNDS==0);

  fesetround(FE_UPWARD);
  assert(FLT_ROUNDS==2);
}

#else

int main()
{
}

#endif
