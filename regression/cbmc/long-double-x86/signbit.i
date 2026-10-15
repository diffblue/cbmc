// Exercises the union-based signbit pattern that the macOS SDK uses for
// `long double`.  See <math.h> on Xcode 16:
//
//   __header_always_inline int __inline_signbitl(long double __x) {
//     union { long double __ld; struct{ unsigned long long __m;
//             unsigned short __sexp; } __p; } __u;
//     __u.__ld = __x;
//     return (int)(__u.__p.__sexp >> 15);
//   }
//
// Before this fix CBMC encoded `long double` on x86_64 as IEEE binary128
// and so `__sexp` (bytes 8-9 of the storage) was always read as zero,
// making `signbit(-1.0L) == 0`.  With x86 80-bit extended modelling the
// sign bit is at bit 79 (i.e. the top of the 16-bit `__sexp` field).
//
// The test is hermetic (no system headers) and provided as `main.i` so
// CBMC parses it without invoking the host's preprocessor.  The
// test.desc fixes `--arch x86_64 --os linux` so CBMC models x86 80-bit
// extended regardless of the host's native long-double layout.

typedef unsigned long long u64;
typedef unsigned short u16;

static int my_signbitl(long double x)
{
  union
  {
    long double ld;
    struct
    {
      u64 m;
      u16 sexp;
    } p;
  } u;
  u.ld = x;
  return (int)(u.p.sexp >> 15);
}

int main(void)
{
  // 1. Negative non-zero values have signbit == 1.
  __CPROVER_assert(my_signbitl(-1.0L) == 1, "signbit(-1.0L) == 1");
  __CPROVER_assert(my_signbitl(-2.0L) == 1, "signbit(-2.0L) == 1");
  __CPROVER_assert(my_signbitl(-0.5L) == 1, "signbit(-0.5L) == 1");

  // 2. Positive values and positive zero have signbit == 0.
  __CPROVER_assert(my_signbitl(1.0L) == 0, "signbit(1.0L) == 0");
  __CPROVER_assert(my_signbitl(2.0L) == 0, "signbit(2.0L) == 0");
  __CPROVER_assert(my_signbitl(0.0L) == 0, "signbit(0.0L) == 0");

  // 3. Negation flips the sign.
  long double v = 3.5L;
  __CPROVER_assert(my_signbitl(v) == 0, "signbit(v) == 0 for v > 0");
  __CPROVER_assert(my_signbitl(-v) == 1, "signbit(-v) == 1");

  return 0;
}
