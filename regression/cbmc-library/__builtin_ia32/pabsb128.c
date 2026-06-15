#include <limits.h>

typedef char __gcc_v16qi __attribute__((__vector_size__(16)));
__gcc_v16qi __builtin_ia32_pabsb128(__gcc_v16qi);

int main()
{
  // Lane 0 is the interesting hardware case: pabsb leaves SCHAR_MIN unchanged
  // (its absolute value is not representable as a signed byte).
  __gcc_v16qi a = (__gcc_v16qi){
    SCHAR_MIN, -2, 3, -4, 5, -6, 7, -8, 9, -10, 11, -12, 13, -14, 15, -16};
  __gcc_v16qi r = __builtin_ia32_pabsb128(a);
  __CPROVER_assert(r[0] == SCHAR_MIN && r[1] == 2 && r[15] == 16, "abs epi8");
  return 0;
}
