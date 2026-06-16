#include <limits.h>

typedef short __gcc_v8hi __attribute__((__vector_size__(16)));
__gcc_v8hi __builtin_ia32_pabsw128(__gcc_v8hi);

int main()
{
  // Lane 0 is the interesting hardware case: pabsw leaves SHRT_MIN unchanged
  // (its absolute value is not representable as a signed 16-bit value).
  __gcc_v8hi a = (__gcc_v8hi){SHRT_MIN, -2, 3, -4, 5, -6, 7, -8};
  __gcc_v8hi r = __builtin_ia32_pabsw128(a);
  __CPROVER_assert(r[0] == SHRT_MIN && r[1] == 2 && r[7] == 8, "abs epi16");
  return 0;
}
