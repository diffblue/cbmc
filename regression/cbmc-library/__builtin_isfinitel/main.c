#include <assert.h>
#include <math.h>

int main()
{
  assert(__builtin_isfinite(1.0));
  assert(!__builtin_isfinite(1.0 / 0.0));
}
