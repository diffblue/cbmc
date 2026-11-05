// Results that round up to a power of two carry out of the significand.
// The non-FPA SMT encoding used to set bit 20 instead of bit 52 of the
// double significand in this case, yielding a tiny subnormal.

int main()
{
  long long i;
  __CPROVER_assume(i >= 0x7FFFFFFFFFFFFE00ll);
  double d = (double)i;
  // Every such i rounds to 0x1p+63 under round-to-nearest-even.
  __CPROVER_assert(d >= 9.2e18, "d rounds to 2^63");

  // Also verify addition that carries out of the significand.
  double x, y;
  __CPROVER_assume(x > 1.9999 && x < 2.0 && y > 0 && y < 1e-10);
  double z = x + y;
  __CPROVER_assert(z >= x, "z >= x after addition");
}
