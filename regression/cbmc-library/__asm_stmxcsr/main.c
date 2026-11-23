#include <assert.h>
#include <fenv.h>

int main()
{
  unsigned csr;
  __asm__("stmxcsr %0" : "=m"(csr));
  assert((csr & 0x6000) == 0);
  fesetround(FE_UPWARD);
  __asm__("stmxcsr %0" : "=m"(csr));
  assert((csr & 0x6000) == 0x4000);
  return 0;
}
