#include <assert.h>
#include <limits.h>
#include <stdlib.h>

int main()
{
  assert(llabs(LLONG_MIN + 1) == LLONG_MAX);
  return 0;
}
