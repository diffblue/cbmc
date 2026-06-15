#include <limits.h>

typedef int __gcc_v8si __attribute__((__vector_size__(32)));
__gcc_v8si __builtin_ia32_pabsd256(__gcc_v8si);

int main()
{
  // Lane 0: pabsd leaves INT_MIN unchanged (no UB in the model).
  __gcc_v8si a = (__gcc_v8si){INT_MIN, -2, 3, -4, 5, -6, 7, -8};
  __gcc_v8si r = __builtin_ia32_pabsd256(a);
  __CPROVER_assert(
    r[0] == INT_MIN && r[1] == 2 && r[7] == 8, "abs epi32 (256)");
  return 0;
}
