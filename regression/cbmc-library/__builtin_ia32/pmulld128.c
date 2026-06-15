#include <limits.h>

typedef int __gcc_v4si __attribute__((__vector_size__(16)));
__gcc_v4si __builtin_ia32_pmulld128(__gcc_v4si, __gcc_v4si);

int main()
{
  // Lane 0 exercises two's-complement wraparound: INT_MAX * 2 keeps only the
  // low 32 bits, 0xFFFFFFFE == -2. Run under --signed-overflow-check (see
  // test.desc).
  __gcc_v4si a = (__gcc_v4si){INT_MAX, 2, 3, 4};
  __gcc_v4si b = (__gcc_v4si){2, 6, 7, 8};
  __gcc_v4si r = __builtin_ia32_pmulld128(a, b);
  __CPROVER_assert(r[0] == -2 && r[3] == 32, "mullo epi32");
  return 0;
}
