// Non-canonical x86 80-bit extended encodings, following x87 hardware (and
// glibc's classification functions):
//
//  - pseudo-NaN (all-ones exponent, integer bit 0, non-zero fraction),
//    pseudo-infinity (all-ones exponent, integer bit 0, zero fraction), and
//    unnormals (exponent neither zero nor all-ones, integer bit 0) are
//    invalid operands: x87 arithmetic yields the default NaN for them, and
//    they compare unordered.  CBMC classifies them as NaN.
//  - a pseudo-denormal (zero exponent, integer bit 1) has the value
//    2^(1-bias) * 1.fraction, i.e., the same as the encoding with exponent 1.
//
// Each encoding is constructed twice: once with member-by-member stores of
// non-constant values, which are never constant folded, and once with a
// constant initialiser, which the simplifier folds into a constant.  The
// test is run with and without --no-simplify, and both forms must agree.
//
// The test is hermetic (no system headers) so that CBMC parses it without
// invoking the host's preprocessor.

typedef unsigned long long u64;
typedef unsigned short u16;

typedef union
{
  long double ld;
  struct
  {
    u64 mantissa;
    u16 sign_exp;
    u16 pad[3];
  } parts;
} ld_layout_t;

static long double make(u64 mantissa, u16 sign_exp)
{
  u64 m;
  u16 se;
  __CPROVER_assume(m == mantissa && se == sign_exp);
  ld_layout_t u = {0};
  u.parts.mantissa = m;
  u.parts.sign_exp = se;
  return u.ld;
}

int main(void)
{
  // pseudo-NaN
  long double pnan = make(0x0000000000000001ULL, 0x7FFF);
  ld_layout_t pnan_c = {.parts = {0x0000000000000001ULL, 0x7FFF, {0, 0, 0}}};
  __CPROVER_assert(__CPROVER_isnanld(pnan), "pseudo-NaN is NaN");
  __CPROVER_assert(__CPROVER_isnanld(pnan_c.ld), "constant pseudo-NaN is NaN");
  __CPROVER_assert(pnan != pnan, "pseudo-NaN is unordered");
  __CPROVER_assert(pnan_c.ld != pnan_c.ld, "constant pseudo-NaN is unordered");

  // pseudo-infinity
  long double pinf = make(0, 0x7FFF);
  ld_layout_t pinf_c = {.parts = {0, 0x7FFF, {0, 0, 0}}};
  __CPROVER_assert(
    __CPROVER_isnanld(pinf) && !__CPROVER_isinfld(pinf),
    "pseudo-infinity is NaN");
  __CPROVER_assert(
    __CPROVER_isnanld(pinf_c.ld) && !__CPROVER_isinfld(pinf_c.ld),
    "constant pseudo-infinity is NaN");

  // unnormal: the bits of 1.0L with the integer bit cleared
  long double unnormal = make(0x0000000000000001ULL, 0x3FFF);
  ld_layout_t unnormal_c = {.parts = {0x0000000000000001ULL, 0x3FFF, {0}}};
  __CPROVER_assert(__CPROVER_isnanld(unnormal), "unnormal is NaN");
  __CPROVER_assert(
    __CPROVER_isnanld(unnormal_c.ld), "constant unnormal is NaN");
  __CPROVER_assert(!(unnormal > 0.5L), "unnormal is unordered");
  __CPROVER_assert(
    __CPROVER_isnanld(unnormal * 1.0L), "arithmetic on unnormal yields NaN");
  __CPROVER_assert(
    __CPROVER_isnanld(unnormal_c.ld * 1.0L),
    "arithmetic on constant unnormal yields NaN");

  // pseudo-denormal: same value as the smallest normal number
  long double pden = make(0x8000000000000000ULL, 0);
  ld_layout_t pden_c = {.parts = {0x8000000000000000ULL, 0, {0, 0, 0}}};
  long double min_normal = make(0x8000000000000000ULL, 1);
  __CPROVER_assert(pden == min_normal, "pseudo-denormal equals 2^-16382");
  __CPROVER_assert(
    pden_c.ld == min_normal, "constant pseudo-denormal equals 2^-16382");
  __CPROVER_assert(
    pden * 4.0L == min_normal * 4.0L, "pseudo-denormal has value 2^-16382");
  __CPROVER_assert(
    pden_c.ld * 4.0L == min_normal * 4.0L,
    "constant pseudo-denormal has value 2^-16382");
  __CPROVER_assert(
    !(pden < min_normal) && pden <= min_normal,
    "pseudo-denormal compares equal");
  __CPROVER_assert(__CPROVER_isnormalld(pden), "pseudo-denormal is normal");
  __CPROVER_assert(
    __CPROVER_isnormalld(pden_c.ld), "constant pseudo-denormal is normal");

  // canonical encodings, for comparison
  long double one = 1.0L;
  __CPROVER_assert(__CPROVER_isnormalld(one), "1.0L is normal");
  long double nan_value = 0.0L / 0.0L;
  __CPROVER_assert(__CPROVER_isnanld(nan_value), "0/0 is NaN");
  long double inf_value = 1.0L / 0.0L;
  __CPROVER_assert(__CPROVER_isinfld(inf_value), "1/0 is infinite");

  return 0;
}
