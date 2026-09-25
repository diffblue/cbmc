// The neon_vector_type attribute (used by Clang's <arm_neon.h>) gives the
// vector size as a lane count rather than in bytes, unlike vector_size.
typedef __attribute__((neon_vector_type(16))) signed char int8x16_t;
typedef __attribute__((neon_vector_type(8))) short int16x8_t;
typedef __attribute__((neon_vector_type(4))) int int32x4_t;
typedef __attribute__((neon_vector_type(2))) double float64x2_t;
// A non-power-of-two lane count whose byte interpretation differs: 3 lanes of
// int is 12 bytes, whereas a byte size of 3 would be rejected as not a
// multiple of sizeof(int).
typedef __attribute__((neon_vector_type(3))) int int32x3_t;

int main()
{
  int8x16_t a = {0};
  a[3] = 7;
  __CPROVER_assert(a[3] == 7, "lane indexing works");
  __CPROVER_assert(sizeof(int8x16_t) == 16, "16 lanes of signed char");
  __CPROVER_assert(sizeof(int16x8_t) == 16, "8 lanes of short");
  __CPROVER_assert(sizeof(int32x4_t) == 16, "4 lanes of int");
  __CPROVER_assert(sizeof(float64x2_t) == 16, "2 lanes of double");
  __CPROVER_assert(
    sizeof(int32x3_t) == 12, "3 lanes of int (lanes, not bytes)");
  return 0;
}
