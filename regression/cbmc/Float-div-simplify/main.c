#include <assert.h>

int main(void)
{
  __CPROVER_rounding_mode = 0; // round to nearest, ties to even
  volatile float x = 0x1.aaaab4p-127f;
  volatile float y = 0x1.000006p+0f;
  // The exact quotient is just above a midpoint between subnormals.
  assert(x / y == 0x1.aaaaacp-127f);
  assert(-x / y == -0x1.aaaaacp-127f);

  // A tiny dividend still needs both a rounding bit and a sticky bit.
  volatile float tiny = 0x1p-149f;
  volatile float small = 0x1.000002p-126f;
  assert(tiny / small == 0x1.fffffcp-24f);
  assert(tiny / 1.0f == tiny);
  assert(tiny / 2.0f == 0.0f);

  __CPROVER_rounding_mode = 2; // round toward positive infinity
  volatile float a = 0x1p-126f;
  volatile float b = 0x1.000002p+0f;
  volatile double c = 0x1p-1022;
  volatile double d = 0x1.0000000000001p+0;
  // Both operands are normal, but the exact quotients are subnormal.
  assert(a / b == a);
  assert(c / d == c);

  __CPROVER_rounding_mode = 1; // round toward negative infinity
  assert(-a / b == -a);
  assert(-c / d == -c);

  __CPROVER_rounding_mode = 3; // round toward zero
  assert(a / b == 0x1.fffffcp-127f);
  assert(-a / b == -0x1.fffffcp-127f);

  __CPROVER_rounding_mode = 4; // round to nearest, ties away from zero
  assert(x / y == 0x1.aaaaacp-127f);
  assert(tiny / 2.0f == tiny);
}
