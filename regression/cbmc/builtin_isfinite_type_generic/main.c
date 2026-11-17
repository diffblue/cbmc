#include <assert.h>

int main()
{
  // GCC's and Clang's __builtin_isfinite is type-generic: a long double
  // beyond the range of double is finite, a float NaN is not
  long double big = 1e400L;
  assert(__builtin_isfinite(big));
  float nan = __builtin_nanf("");
  assert(!__builtin_isfinite(nan));
  assert(__builtin_isfinite(1.0f) && __builtin_isfinite(1.0));
  __CPROVER_assert(0, "WRONG (must FAIL)");
  return 0;
}
