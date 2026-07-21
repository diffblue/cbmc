#include <assert.h>

unsigned long __isoc23_strtoul(const char *, char **, int);

int main()
{
  // C23 7.24.1.7p3: the C23 variant accepts a 0b prefix for base 0 and 2
  assert(__isoc23_strtoul("0b11", 0, 0) == 3);
  return 0;
}
