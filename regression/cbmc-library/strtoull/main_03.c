#include <assert.h>

unsigned long long __isoc23_strtoull(const char *, char **, int);

int main()
{
  // C23 7.24.1.7p3: the C23 variant accepts a 0b prefix for base 0 and 2
  assert(__isoc23_strtoull("0B11", 0, 0) == 3);
  assert(__isoc23_strtoull("-0b1", 0, 2) == (unsigned long long)-1);
  return 0;
}
