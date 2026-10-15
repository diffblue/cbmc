// Modern x86 hardware treats x86 80-bit extended encodings with the
// explicit integer bit cleared as invalid wherever the value would
// otherwise be classified as normal/infinity/NaN:
//
//  - integer bit = 0 with non-zero biased exponent: "pseudo-denormal"
//    or "unsupported" -- raises FE_INVALID, not a normal value.
//  - integer bit = 0 with all-ones exponent + zero fraction:
//    "pseudo-infinity" -- raises FE_INVALID, not infinity.
//  - integer bit = 0 with all-ones exponent + non-zero fraction:
//    "pseudo-NaN" -- raises FE_INVALID, not a NaN.
//
// CBMC's classification helpers (isnan, isinf, isnormal) follow the
// hardware convention: they require the integer bit to be set before
// classifying a value as NaN/Inf/normal.  This test constructs each
// pseudo-encoding via union and confirms the helpers reject them.
//
// The test is hermetic (no system headers) and provided as `main.i`
// so CBMC parses it without invoking the host's preprocessor.  This
// avoids host-specific issues (e.g. mingw <math.h> constructs CBMC
// cannot parse, BSDs lacking gcc, arm64 hosts lacking x86 cross
// tooling) provided the test.desc fixes `--arch x86_64 --os linux`.

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

int main(void)
{
  // 1. A pseudo-NaN: exponent all-ones, fraction non-zero, but the
  //    explicit integer bit (top bit of mantissa) is 0.
  ld_layout_t pseudo_nan;
  pseudo_nan.parts.mantissa = 0x0000000000000001ULL; // int_bit=0, frac!=0
  pseudo_nan.parts.sign_exp = 0x7FFF;                // exp=all-ones, sign=0
  pseudo_nan.parts.pad[0] = 0;
  pseudo_nan.parts.pad[1] = 0;
  pseudo_nan.parts.pad[2] = 0;
  __CPROVER_assert(!__CPROVER_isnanld(pseudo_nan.ld), "pseudo-NaN is not NaN");

  // 2. A pseudo-Infinity: exponent all-ones, fraction zero, integer
  //    bit 0.
  ld_layout_t pseudo_inf;
  pseudo_inf.parts.mantissa = 0x0000000000000000ULL; // int_bit=0, frac=0
  pseudo_inf.parts.sign_exp = 0x7FFF;                // exp=all-ones, sign=0
  pseudo_inf.parts.pad[0] = 0;
  pseudo_inf.parts.pad[1] = 0;
  pseudo_inf.parts.pad[2] = 0;
  __CPROVER_assert(
    !__CPROVER_isinfld(pseudo_inf.ld), "pseudo-Inf is not infinity");

  // 3. A pseudo-denormal: non-zero exponent, integer bit 0.  Hardware
  //    treats this as a denormal-like; CBMC's `isnormal` rejects it.
  ld_layout_t pseudo_denormal;
  pseudo_denormal.parts.mantissa = 0x0000000000000001ULL; // int_bit=0
  pseudo_denormal.parts.sign_exp = 0x3FFF;                // exp=16383
  pseudo_denormal.parts.pad[0] = 0;
  pseudo_denormal.parts.pad[1] = 0;
  pseudo_denormal.parts.pad[2] = 0;
  __CPROVER_assert(
    !__CPROVER_isnormalld(pseudo_denormal.ld),
    "pseudo-denormal is not normal");

  // 4. By contrast, a real normal value (1.0L) is classified normal,
  //    a real NaN is classified NaN, and a real infinity as inf.
  long double one = 1.0L;
  __CPROVER_assert(__CPROVER_isnormalld(one), "1.0L is normal");

  long double nan_value = 0.0L / 0.0L;
  __CPROVER_assert(__CPROVER_isnanld(nan_value), "0/0 is NaN");

  long double inf_value = 1.0L / 0.0L;
  __CPROVER_assert(__CPROVER_isinfld(inf_value), "1/0 is infinite");

  return 0;
}
