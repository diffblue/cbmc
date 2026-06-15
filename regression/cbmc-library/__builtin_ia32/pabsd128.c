#include <limits.h>

typedef int __gcc_v4si __attribute__((__vector_size__(16)));
__gcc_v4si __builtin_ia32_pabsd128(__gcc_v4si);

int main()
{
  // Lane 0 is the interesting hardware case: pabsd leaves INT_MIN unchanged
  // (its absolute value is not representable), and it is also the input that
  // exposed the -INT_MIN signed-overflow UB in the previous model.
  __gcc_v4si a = (__gcc_v4si){INT_MIN, -2, 3, -4};
  __gcc_v4si r = __builtin_ia32_pabsd128(a);
  __CPROVER_assert(r[0] == INT_MIN && r[1] == 2 && r[3] == 4, "abs epi32");
  return 0;
}
