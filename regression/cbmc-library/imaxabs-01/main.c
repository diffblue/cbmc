#include <assert.h>
#include <inttypes.h>
#include <stdlib.h>

int main()
{
  assert(imaxabs(INTMAX_MIN + 1) == INTMAX_MAX);
  return 0;
}
