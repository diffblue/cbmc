#include <assert.h>
#include <inttypes.h>

int main()
{
#if defined(__clang__) || defined(_GNUC_)
  // GCC actually only supports __builtin_bit_cast in C++ mode, but we do it for
  // C as well.
  float f = 1.5;
  assert((int32_t)f == 1);
  int32_t i = __builtin_bit_cast(int32_t, f);
  assert(i != 1);
  assert(__builtin_bit_cast(float, i) == f);
#endif
}
