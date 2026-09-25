// On x86_64 (Linux, macOS, FreeBSD) `long double` is the 80-bit x87
// extended-precision format stored in 16 bytes (12 on i386).  The stored
// representation is, low to high (i.e. byte 0 is the LSB):
//
//   bits   0 ..  62  : explicit fraction (62 bits, no implicit leading 1)
//   bit       63     : explicit integer bit (J-bit) -- 1 for normal/inf/NaN,
//                      0 for zero/denormal
//   bits  64 ..  78  : biased 15-bit exponent
//   bit       79     : sign bit
//   bits  80 .. 127  : storage padding (zero on Linux/macOS)
//
// The bias is 16383, so a finite normal value v is encoded as
//   (-1)^sign * 2^(exp - 16383) * (1.f)
// where the leading 1 is stored explicitly in bit 63.
//
// The ground-truth byte sequences below were captured on real macOS-15
// x86_64 hardware (Xcode 16.4, Apple clang 17.0.0):
//
//   1.0L  -> 00 00 00 00 00 00 00 80 ff 3f 00 00 00 00 00 00
//   -1.0L -> 00 00 00 00 00 00 00 80 ff bf 00 00 00 00 00 00
//   2.0L  -> 00 00 00 00 00 00 00 80 00 40 00 00 00 00 00 00
//   0.5L  -> 00 00 00 00 00 00 00 80 fe 3f 00 00 00 00 00 00
//   0.0L  -> 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00
//
// The test is hermetic (no system headers) and provided as `main.i` so
// CBMC parses it without invoking the host's preprocessor.  The
// test.desc fixes `--arch x86_64 --os linux` so CBMC models x86 80-bit
// extended in 16-byte storage regardless of the host's native long
// double layout.

typedef unsigned char u8;
typedef unsigned short u16;
typedef unsigned long long u64;

typedef union
{
  long double ld;
  u8 bytes[16];
  struct
  {
    u64 mantissa;
    u16 sign_exp;
    u16 pad[3];
  } parts;
} ld_layout_t;

int main(void)
{
  // 1. Storage size is 16 bytes.
  __CPROVER_assert(sizeof(long double) == 16, "16-byte storage");

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

  // 4. Scaling by 2 increments the biased exponent by 1.
  ld_layout_t two;
  two.ld = 2.0L;
  __CPROVER_assert(
    two.parts.mantissa == 0x8000000000000000ULL, "mantissa for 2.0L");
  __CPROVER_assert(two.parts.sign_exp == 0x4000, "sign_exp for 2.0L");

  // 5. Scaling by 1/2 decrements the biased exponent by 1.
  ld_layout_t half;
  half.ld = 0.5L;
  __CPROVER_assert(
    half.parts.mantissa == 0x8000000000000000ULL, "mantissa for 0.5L");
  __CPROVER_assert(half.parts.sign_exp == 0x3FFE, "sign_exp for 0.5L");

  // 6. Zero has all bits clear (in particular no explicit integer bit).
  ld_layout_t zero;
  zero.ld = 0.0L;
  __CPROVER_assert(zero.parts.mantissa == 0ULL, "mantissa for 0.0L");
  __CPROVER_assert(zero.parts.sign_exp == 0, "sign_exp for 0.0L");

  // 7. The byte view matches the captured native sequence for 1.0L.
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
  __CPROVER_assert(one.bytes[12] == 0x00, "byte 12");
  __CPROVER_assert(one.bytes[13] == 0x00, "byte 13");
  __CPROVER_assert(one.bytes[14] == 0x00, "byte 14");
  __CPROVER_assert(one.bytes[15] == 0x00, "byte 15");

  return 0;
}
