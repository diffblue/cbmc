// Calls of the __builtin_neon_* builtins as Clang's <arm_neon.h> makes them.
// The vector types are spelt with vector_size so that this test does not
// depend on the neon_vector_type attribute.
typedef signed char int8x8_t __attribute__((vector_size(8)));
typedef unsigned char uint8x8_t __attribute__((vector_size(8)));
typedef unsigned short uint16x8_t __attribute__((vector_size(16)));
typedef double float64x1_t __attribute__((vector_size(8)));

int main()
{
  int8x8_t a = {1, 2, 3, 4, 5, 6, 7, 8};
  int8x8_t b = {8, 7, 6, 5, 4, 3, 2, 1};

  // A polymorphic builtin: the last argument encodes the lane type.
  _Static_assert(sizeof(__builtin_neon_vabd_v(a, b, 0)) == 8, "vabd_v");
  int8x8_t d = (int8x8_t)__builtin_neon_vabd_v(a, b, 0);
  _Static_assert(sizeof(__builtin_neon_vget_lane_i8(d, 0)) == 1, "lane_i8");

#ifdef __aarch64__
  // Across-vector reductions of unsigned vectors.
  uint8x8_t u8 = {1, 2, 3, 4, 5, 6, 7, 8};
  _Static_assert(sizeof(__builtin_neon_vaddv_u8(u8)) == 1, "vaddv_u8");
  uint16x8_t u16 = {1, 2, 3, 4, 5, 6, 7, 8};
  _Static_assert(sizeof(__builtin_neon_vaddvq_u16(u16)) == 2, "vaddvq_u16");

  // A one-lane vector.
  float64x1_t f64 = {1.0};
  _Static_assert(sizeof(__builtin_neon_vget_lane_f64(f64, 0)) == 8, "f64");

  // A 64-bit integer scalar.
  _Static_assert(sizeof(__builtin_neon_vabsd_s64(-1LL)) == 8, "vabsd_s64");

  // A half-precision scalar (from Clang's arm_fp16.td).
  _Static_assert(
    sizeof(__builtin_neon_vabsh_f16((__fp16)-1.0f)) == 2, "vabsh_f16");
#endif

  __CPROVER_assert(0, "reachable");
  return 0;
}
