// Test floating-point classification predicates: isfinite, isinf (signed).

#include <assert.h>
#include <math.h>

int main()
{
  float pos_inf = 1.0f / 0.0f;
  float neg_inf = -1.0f / 0.0f;
  float nan_val = 0.0f / 0.0f;
  float normal = 1.5f;
  float zero = 0.0f;

  // isfinite
  assert(isfinite(normal));
  assert(isfinite(zero));
  assert(!isfinite(pos_inf));
  assert(!isfinite(neg_inf));
  assert(!isfinite(nan_val));

  // isinf with sign
  assert(isinf(pos_inf) && pos_inf > 0);
  assert(isinf(neg_inf) && neg_inf < 0);
  assert(!isinf(normal));
  assert(!isinf(nan_val));

  return 0;
}
