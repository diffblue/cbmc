// Based on Z3#4843: Signed zero handling.
// IEEE 754: -0 == +0 (comparison), but they are distinct bit patterns.
// fmax(-0, +0) should return +0 per IEEE 754-2019.

#include <assert.h>
#include <math.h>

int main()
{
  // -0 == +0 in comparison
  float nz = -0.0f;
  float pz = +0.0f;
  assert(nz == pz);

  // But they have different signs
  assert(signbit(nz));
  assert(!signbit(pz));

  // Negation flips sign of zero
  float neg_pz = -pz;
  assert(signbit(neg_pz));

  float neg_nz = -nz;
  assert(!signbit(neg_nz));

  return 0;
}
