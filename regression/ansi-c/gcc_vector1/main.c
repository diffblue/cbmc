// Debian package pixman

#include <assert.h>
#include <stdio.h>

int main()
{
  #if defined(__GNUC__) && !defined(__clang__)
  unsigned int __attribute__((vector_size (4*sizeof(unsigned int)))) v1 = { 1, 1, 1, 1 };
  unsigned int __attribute__((vector_size (4*sizeof(unsigned int)))) v3 = { 3, 3, 3, 3 };

  assert(sizeof(v1==v3)==sizeof(int)*4);

  // accepted by GCC, but not Clang
  assert((v3 == (v1<<1)+v1)[0]);

  unsigned int __attribute__((vector_size (4*sizeof(unsigned int)))) b2 = { 3, 3, 3, 3 };
  unsigned int __attribute__((vector_size (4*sizeof(unsigned int)))) b1 = { 1, 1, 1, 1 };
  printf("(b2>b1)[0]=%d\n", (b2>b1)[0]); // -1
  printf("b2[0]>b1[0]=%d\n", b2[0]>b1[0]); // 1
  b2|=(b2>=b1);
  assert(b2[0]>=3); // that's really the only guarantee
  #endif

  return 0;
}
