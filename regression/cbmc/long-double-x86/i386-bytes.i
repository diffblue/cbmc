// Same byte-layout invariants as long-double-x86-bytes but for i386
// (32-bit x86), where `long double` is the 80-bit x87 extended-precision
// format stored in 12 bytes.  The 80-bit value layout is identical to
// x86_64; only the storage container size differs.
//
// The test is hermetic (no system headers) and provided as `main.i`
// so CBMC parses it without invoking the host's preprocessor.  It can
// therefore run on any host (in particular hosts without i386
// cross-compilation tooling installed) provided the test.desc fixes
// `--i386-linux` so CBMC models the 12-byte layout regardless.

typedef unsigned char u8;
typedef unsigned short u16;
typedef unsigned long long u64;

typedef union
{
  long double ld;
  u8 bytes[12];
  struct
  {
    u64 mantissa;
    u16 sign_exp;
    u16 pad;
  } parts;
} ld_layout_t;

int main(void)
{
  // 1. Storage size is 12 bytes on i386.
  __CPROVER_assert(sizeof(long double) == 12, "12-byte storage");

  // 2. The 80-bit value of 1.0L is mantissa = 0x8000000000000000,
  //    sign_exp = 0x3FFF (sign 0, biased exponent 0x3FFF = 16383).
  ld_layout_t one;
  one.ld = 1.0L;
  __CPROVER_assert(
    one.parts.mantissa == 0x8000000000000000ULL, "mantissa for 1.0L");
  __CPROVER_assert(one.parts.sign_exp == 0x3FFF, "sign_exp for 1.0L");

  // 3. Negation flips the sign bit at the top of sign_exp.
  ld_layout_t neg_one;
  neg_one.ld = -1.0L;
  __CPROVER_assert(
    neg_one.parts.mantissa == 0x8000000000000000ULL, "mantissa for -1.0L");
  __CPROVER_assert(neg_one.parts.sign_exp == 0xBFFF, "sign_exp for -1.0L");

  // 4. The byte view matches the 12-byte little-endian sequence.
  __CPROVER_assert(one.bytes[0] == 0x00, "byte 0");
  __CPROVER_assert(one.bytes[1] == 0x00, "byte 1");
  __CPROVER_assert(one.bytes[2] == 0x00, "byte 2");
  __CPROVER_assert(one.bytes[3] == 0x00, "byte 3");
  __CPROVER_assert(one.bytes[4] == 0x00, "byte 4");
  __CPROVER_assert(one.bytes[5] == 0x00, "byte 5");
  __CPROVER_assert(one.bytes[6] == 0x00, "byte 6");
  __CPROVER_assert(one.bytes[7] == 0x80, "byte 7");
  __CPROVER_assert(one.bytes[8] == 0xFF, "byte 8");
  __CPROVER_assert(one.bytes[9] == 0x3F, "byte 9");
  __CPROVER_assert(one.bytes[10] == 0x00, "byte 10");
  __CPROVER_assert(one.bytes[11] == 0x00, "byte 11");

  return 0;
}
