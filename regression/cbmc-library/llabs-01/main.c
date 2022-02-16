#include <assert.h>
#include <stdlib.h>

#include <limits.h>

int main()
{
  assert(llabs(LLONG_MIN + 1) == LLONG_MAX);
  return 0;
}
