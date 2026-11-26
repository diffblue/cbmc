#include <stdint.h>

int nondet_int(void);

int main()
{
  if(nondet_int())
  {
    // Write to an address outside the declared region
    volatile char *p = (volatile char *)0x3000;
    *p = 42;
  }
  else
  {
    // Read from an address outside the declared region
    volatile char *q = (volatile char *)0x4000;
    char v = *q;
  }

  return 0;
}
