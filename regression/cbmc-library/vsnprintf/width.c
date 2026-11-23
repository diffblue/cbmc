#include <assert.h>
#include <stdio.h>
#include <string.h>

int main()
{
  // the field width is larger than the unwinding bound, but only as many
  // padding characters as fit the buffer are written
  char b[4];
  int r = snprintf(b, sizeof b, "%100d", 1);
  assert(r == 100 && strcmp(b, "   ") == 0);
  r = snprintf(b, sizeof b, "%-100s|", "ab");
  assert(r == 101 && strcmp(b, "ab ") == 0);
  r = snprintf(b, sizeof b, "%.100d", 1);
  assert(r == 100 && strcmp(b, "000") == 0);
  return 0;
}
