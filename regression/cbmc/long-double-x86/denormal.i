// Denormal results of x86 80-bit extended `long double` arithmetic: a
// denormal has a zero exponent and a cleared integer bit.  The smallest
// normal number 2^-16382 is built through a union to avoid a
// 16382-iteration loop.
//
// The test is hermetic (no system headers) and provided as `denormal.i` so
// CBMC parses it without invoking the host's preprocessor.

typedef union
{
  long double ld;
  struct
  {
    unsigned long long m;
    unsigned short se;
    unsigned short pad[3];
  } p;
} ld_t;

int main(void)
{
  ld_t sn = {0};
  sn.p.m = 0x8000000000000000ULL;
  sn.p.se = 1;
  long double m = sn.ld;

  long double denormal = m / 4.0L; // 2^-16384
  ld_t dd;
  dd.ld = denormal;
  __CPROVER_assert(
    dd.p.se == 0 && dd.p.m == 0x2000000000000000ULL, "denormal has J=0");
  __CPROVER_assert(!__CPROVER_isnormalld(denormal), "denormal is not normal");
  __CPROVER_assert(denormal * 4.0L == m, "denormal round trip");

  // Rounding the largest denormal up yields the smallest normal number,
  // which has the integer bit set.
  ld_t ld = {0};
  ld.p.m = 0x7fffffffffffffffULL;
  long double largest_denormal = ld.ld;
  __CPROVER_rounding_mode = 2; // upward
  long double sum = largest_denormal + largest_denormal / 0x1p64L;
  ld_t sd;
  sd.ld = sum;
  __CPROVER_assert(
    sd.p.se == 1 && sd.p.m == 0x8000000000000000ULL,
    "rounding up into the normal range sets J");

  return 0;
}
