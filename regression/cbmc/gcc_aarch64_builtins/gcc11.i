// GCC 11's <arm_neon.h> defines the tuple types itself and passes the tuples
// to the structure load builtins as opaque values.
typedef __Int8x8_t int8x8_t;
typedef struct int8x8x2_t
{
  int8x8_t val[2];
} int8x8x2_t;

int8x8x2_t vld2_s8(const signed char *p)
{
  int8x8x2_t ret;
  __builtin_aarch64_simd_oi __o;
  __o = __builtin_aarch64_ld2v8qi((const __builtin_aarch64_simd_qi *)p);
  ret.val[0] = (int8x8_t)__builtin_aarch64_get_dregoiv8qi(__o, 0);
  ret.val[1] = (int8x8_t)__builtin_aarch64_get_dregoiv8qi(__o, 1);
  return ret;
}

int main()
{
  signed char buffer[16] = {0};
  int8x8x2_t pair = vld2_s8(buffer);
  __CPROVER_assert(0, "reachable");
  return 0;
}
