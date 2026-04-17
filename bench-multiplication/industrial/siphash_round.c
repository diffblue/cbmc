#include <stdint.h>
// SipHash round function (simplified)
static void sipround(uint64_t *v0, uint64_t *v1, uint64_t *v2, uint64_t *v3) {
  *v0 += *v1; *v1 = (*v1 << 13) | (*v1 >> 51); *v1 ^= *v0;
  *v0 = (*v0 << 32) | (*v0 >> 32);
  *v2 += *v3; *v3 = (*v3 << 16) | (*v3 >> 48); *v3 ^= *v2;
  *v0 += *v3; *v3 = (*v3 << 21) | (*v3 >> 43); *v3 ^= *v0;
  *v2 += *v1; *v1 = (*v1 << 17) | (*v1 >> 47); *v1 ^= *v2;
  *v2 = (*v2 << 32) | (*v2 >> 32);
}
int main() {
  uint64_t v0, v1, v2, v3;
  uint64_t s0=v0, s1=v1, s2=v2, s3=v3;
  sipround(&v0, &v1, &v2, &v3);
  sipround(&s0, &s1, &s2, &s3);
  __CPROVER_assert(v0==s0 && v1==s1 && v2==s2 && v3==s3, "deterministic");
}
