// Debian package pixman

#include <assert.h>

int main()
{
#if defined(__GNUC__) && !defined(__clang__)
  unsigned int __attribute__((vector_size (4*sizeof(unsigned int)))) v1 = { 1, 1, 1, 1 };
  unsigned int __attribute__((vector_size (4*sizeof(unsigned int)))) v3 = { 3, 3, 3, 3 };

  // accepted by GCC, but not Clang
  assert((v3 == (v1<<1)+v1)[0]);;
#endif

  return 0;
}
