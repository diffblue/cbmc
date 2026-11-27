// The built-in types that GCC provides for AArch64, as GCC 16's
// arm_private_fp8.h and arm_private_neon_types.h use them.
typedef __mfp8 mfloat8_t;
typedef __Int8x8_t int8x8_t;
typedef __Uint64x2_t uint64x2_t;
typedef __Bfloat16x8_t bfloat16x8_t;
typedef __Poly128_t poly128_t;

_Static_assert(sizeof(mfloat8_t) == 1, "mfloat8_t");
_Static_assert(sizeof(int8x8_t) == 8, "int8x8_t");
_Static_assert(sizeof(uint64x2_t) == 16, "uint64x2_t");
_Static_assert(sizeof(bfloat16x8_t) == 16, "bfloat16x8_t");
_Static_assert(sizeof(poly128_t) == 16, "poly128_t");

int main()
{
  int8x8_t v = {1, 2, 3, 4, 5, 6, 7, -8};
  __CPROVER_assert(v[7] == -8, "lanes are signed");
  uint64x2_t w = {1, 2};
  __CPROVER_assert(w[0] - w[1] > 0, "lanes are unsigned");
  return 0;
}
