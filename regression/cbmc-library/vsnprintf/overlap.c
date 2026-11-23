#include <stdio.h>

int main()
{
  char b[16] = "abc";
  // the source of %s is the destination: undefined behaviour (restrict)
  snprintf(b, sizeof b, "x%s", b);
  // the source follows the characters written: no overlap
  char c[16] = "........xyz";
  snprintf(c, 4, "%s", c + 8);
  return 0;
}
