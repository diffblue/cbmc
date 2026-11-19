#include <assert.h>
#include <stdio.h>

int main(void)
{
  char b[4];
  // C11 7.21.6.5p3: snprintf returns the number of characters that would have
  // been written had the buffer been large enough
  int r = snprintf(b, sizeof b, "%s", "hello");
  assert(r <= 4); // must FAIL: r is 5
  assert(r == 5);
  return 0;
}
