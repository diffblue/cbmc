#include <assert.h>
#include <fenv.h>

int main()
{
  unsigned short cw;
#ifdef __GNUC__
  __asm__("fstcw %0" : "=m"(cw));
#else
  __asm { fstcw cw; }
#endif
  assert((cw & 0xc00) == 0);
  fesetround(FE_UPWARD);
#ifdef __GNUC__
  __asm__("fstcw %0" : "=m"(cw));
#else
  __asm { fstcw cw; }
#endif
  assert((cw & 0xc00) == 0x800);
}
