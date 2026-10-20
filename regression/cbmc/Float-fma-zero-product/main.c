#include <assert.h>
#include <math.h>
#include <stdint.h>
#include <string.h>

#ifdef __CPROVER__
uint32_t nondet_u32(void);
#endif

static uint64_t bits(double d)
{
  uint64_t b;
  memcpy(&b, &d, sizeof(b));
  return b;
}

int main(void)
{
  // fma(x, 0, z) == z when x is finite and z is subnormal. The product
  // exponent was computed from the operand exponents even when one operand
  // was zero, causing the addend to be shifted out during alignment.
#ifdef __CPROVER__
  uint32_t ux = nondet_u32();
  __CPROVER_assume(ux == 0x63b229f1u || ux == 0x63b229f2u);
#else
  uint32_t ux = 0x63b229f1u;
#endif
  uint32_t uz = 0x80343e4cu; // subnormal: -4.797794e-39f
  float x, z, r;
  uint32_t ur;
  memcpy(&x, &ux, sizeof(float));
  memcpy(&z, &uz, sizeof(float));
  r = fmaf(x, 0.0f, z);
  memcpy(&ur, &r, sizeof(float));
  if(ux == 0x63b229f1u)
    assert(ur == 0x80343e4cu); // result must be z

  // An exact zero result is +0 unless both the product and the addend are
  // negative (round to nearest).
  volatile double three = 3.0, zero = 0.0, nzero = -0.0, one = 1.0;
  assert(bits(fma(three, zero, nzero)) == 0);
  assert(bits(fma(nzero, one, nzero)) == 0x8000000000000000ull);

  // An infinite product determines the sign of the result.
  volatile double ninf = -INFINITY, tiny = 1e-310;
  assert(fma(one, ninf, tiny) == -INFINITY);
  return 0;
}
