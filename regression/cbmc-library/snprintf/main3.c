#include <assert.h>
#include <stdio.h>

int main(void)
{
  char b[4];
  // C11 7.21.6.5p2: output beyond the size-1st character is discarded, and a
  // null character is written at the end of the characters actually written
  int r = snprintf(b, sizeof b, "%s", "hello");
  if(r >= 0)
    assert(b[r < 3 ? r : 3] == 0);

  return 0;
}
