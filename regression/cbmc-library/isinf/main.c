#include <assert.h>
#include <float.h>
#include <math.h>

#ifdef __GNUC__

void f00(float f)
{
  if(f > 0x1.FFFFFEp+127)
  {
    assert(isinf(f));
  }
}

#endif

int main(void)
{
#ifdef __GNUC__
  float f;

  f00(f);
#endif

#if !defined(__clang__) && defined(__GNUC__)
  assert(__builtin_isinf(DBL_MAX + DBL_MAX) == 1);
  assert(__builtin_isinf(0.0) == 0);
  assert(__builtin_isinf(-(DBL_MAX + DBL_MAX)) == 1);

  assert(__builtin_isinf_sign(DBL_MAX + DBL_MAX) == 1);
  assert(__builtin_isinf_sign(0.0) == 0);
  assert(__builtin_isinf_sign(-(DBL_MAX + DBL_MAX)) == -1);

  _Static_assert(!__builtin_isinf(0.0), "__builtin_isinf is constant");

  _Static_assert(
    __builtin_isinf_sign(0.0) == 0, "__builtin_isinf_sign is constant");
#endif

  return 0;
}
