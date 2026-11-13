#include <assert.h>
#include <float.h>
#include <math.h>

int main()
{
#if !defined(__clang__) && defined(__GNUC__)
  _Static_assert(__builtin_isnormal(DBL_MIN), "__builtin_isnormal is constant");
#endif

  return 0;
}
