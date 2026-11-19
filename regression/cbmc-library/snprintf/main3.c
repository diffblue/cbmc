#include <assert.h>
#include <stdio.h>
#include <string.h>

int main(void)
{
  char b[4];
  // C11 7.21.6.5p2: output beyond the size-1st character is discarded, and a
  // null character is written at the end of the characters actually written
  snprintf(b, sizeof b, "%s", "hello");
  assert(b[3] == '\0');
  assert(strcmp(b, "hel") == 0);
  return 0;
}
