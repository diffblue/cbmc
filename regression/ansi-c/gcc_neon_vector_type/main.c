// The neon_vector_type attribute (used by Clang's <arm_neon.h>) gives the
// vector size as a lane count rather than in bytes, unlike vector_size.

#define CONCAT(a, b) a##b
#define CONCAT2(a, b) CONCAT(a, b)

#define STATIC_ASSERT(condition)                                               \
  int CONCAT2(some_array, __LINE__)[(condition) ? 1 : -1]

typedef __attribute__((neon_vector_type(16))) signed char int8x16_t;
typedef __attribute__((neon_vector_type(8))) short int16x8_t;
typedef __attribute__((neon_vector_type(4))) int int32x4_t;
typedef __attribute__((neon_vector_type(2))) double float64x2_t;

// 2 lanes of int is 8 bytes, whereas a byte size of 2 would be rejected as not
// a multiple of sizeof(int).
typedef __attribute__((__neon_vector_type__(2))) int int32x2_t;

// <arm_neon.h> uses neon_polyvector_type for the polynomial types, again with
// a lane count.
typedef __attribute__((neon_polyvector_type(8))) unsigned char poly8x8_t;
typedef __attribute__((__neon_polyvector_type__(8))) unsigned short poly16x8_t;

STATIC_ASSERT(sizeof(int8x16_t) == 16);
STATIC_ASSERT(sizeof(int16x8_t) == 16);
STATIC_ASSERT(sizeof(int32x4_t) == 16);
STATIC_ASSERT(sizeof(float64x2_t) == 16);
STATIC_ASSERT(sizeof(int32x2_t) == 8);
STATIC_ASSERT(sizeof(poly8x8_t) == 8);
STATIC_ASSERT(sizeof(poly16x8_t) == 16);

int main()
{
  int32x2_t v = {1, 2};
  return v[1] - 2;
}
