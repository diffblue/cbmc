#include <assert.h>

main()
{
  float a;
  double b;

  // various forms of floating-point literals
  a=1.25L;
  assert(a==1.25);

  b=1.250;
  assert(b==1.25);
  
  // with exponent
  a=0.5e2;
  assert(a==50);

  // hex
  a=0x1.4p+4;
  assert(a==20);
}
