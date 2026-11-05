// The padding bits of x86 80-bit extended `long double` in its 16-byte
// storage are not part of the value: comparisons and classification must
// ignore them, for both constant and symbolic values.
//
// The test is hermetic (no system headers) and provided as `padding.i` so
// CBMC parses it without invoking the host's preprocessor.

typedef union
{
  long double ld;
  unsigned char b[16];
} ld_t;

int main(void)
{
  ld_t x, y;
  x.ld = 1.5L;
  y = x;
  y.b[12] = 0x5a; // differs only in storage padding
  __CPROVER_assert(x.ld == y.ld, "padding ignored by ==");
  __CPROVER_assert(!(x.ld < y.ld) && x.ld <= y.ld, "padding ignored by <, <=");

  long double z;
  ld_t w;
  w.ld = z;
  w.b[15] ^= 1;
  __CPROVER_assert(
    __CPROVER_isnanld(z) || w.ld == z, "symbolic: padding ignored by ==");
  __CPROVER_assert(
    __CPROVER_isnanld(z) || (w.ld <= z && z <= w.ld && !(w.ld < z)),
    "symbolic: padding ignored by <, <=");

  ld_t nz = {0};
  nz.b[11] = 0xff; // +0.0 with non-zero padding
  __CPROVER_assert(nz.ld == 0.0L && nz.ld == -0.0L, "is_zero ignores padding");

  return 0;
}
