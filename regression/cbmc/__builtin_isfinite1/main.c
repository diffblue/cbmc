// __builtin_isfinite is type-generic: glibc's isfinite(x) expands to it.
#include <assert.h>
#include <float.h>

int main()
{
  assert(__builtin_isfinite(FLT_MAX));
  assert(__builtin_isfinite(DBL_MAX));
  assert(__builtin_isfinite(LDBL_MAX));
  assert(!__builtin_isfinite(1.0f / 0.0f));
  assert(!__builtin_isfinite(1.0 / 0.0));
  assert(!__builtin_isfinite(1.0l / 0.0l));
  return 0;
}
