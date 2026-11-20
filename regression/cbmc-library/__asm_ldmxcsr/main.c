#include <assert.h>
#include <fenv.h>

int main()
{
  unsigned csr = 0x6000; // round toward zero
  __asm__("ldmxcsr %0" : : "m"(csr));
  assert(fegetround() == FE_TOWARDZERO);
  return 0;
}
