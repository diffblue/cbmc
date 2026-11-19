#include <assert.h>
#include <stdio.h>

int main(void)
{
  // C11 7.21.6.5p2, p3: with size 0 nothing is written, and the result is the
  // length of the output, which programs use to allocate a buffer
  int n = snprintf(NULL, 0, "%d", 12345);
  assert(n == 5);
  return 0;
}
