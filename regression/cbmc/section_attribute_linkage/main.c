#include "other.h"

#include <assert.h>

int main()
{
  p.x = 123;

  // valid assertion, gets proof
  assert(p.x == 123);

  int i = get();

  // valid assertion, but gets cex
  assert(i == 123);

  return 0;
}
