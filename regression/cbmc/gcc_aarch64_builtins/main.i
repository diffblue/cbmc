// The built-in types and functions that GCC 12 and later provide for
// <arm_neon.h> and <arm_acle.h>, as these headers use them.
#pragma GCC aarch64 "arm_neon.h"
typedef __Int8x8_t int8x8_t;
typedef __Uint8x8_t uint8x8_t;
typedef __mfp8 mfloat8_t;

_Static_assert(sizeof(int8x8_t) == 8, "int8x8_t");
_Static_assert(sizeof(mfloat8_t) == 1, "mfloat8_t");
// declared by the pragma
_Static_assert(sizeof(int8x8x2_t) == 16, "int8x8x2_t");
_Static_assert(sizeof(__Float64x2_t) == 16, "__Float64x2_t");

int8x8x2_t vld2_s8(const signed char *p)
{
  // declared by the pragma
  return __builtin_aarch64_ld2v8qi((const __builtin_aarch64_simd_qi *)p);
}

#pragma GCC aarch64 "arm_acle.h"
_Static_assert(sizeof(__arm_data512_t) == 64, "__arm_data512_t");

int main()
{
  signed char buffer[16] = {0};
  int8x8x2_t pair = vld2_s8(buffer);
  int8x8_t a = pair.val[0];
  // declared on demand
  int8x8_t b = __builtin_aarch64_ld1v8qi(buffer);
  unsigned char sum =
    __builtin_aarch64_reduc_plus_scal_v8qi_uu((uint8x8_t)(a + b));
  // GCC 13 and later register vreinterpret_* themselves
  uint8x8_t u = vreinterpret_u8_s8(a);
  _Static_assert(sizeof(vreinterpret_u8_s8(a)) == 8, "vreinterpret");

  __CPROVER_assert(0, "reachable");
  return 0;
}
