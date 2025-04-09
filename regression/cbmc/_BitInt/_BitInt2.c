// _BitInt is a C23 feature
#include <assert.h>

int main()
{
  // casts
  assert((_BitInt(4))17 == 1);
  assert((_BitInt(4)) - 1 == -1);
  assert((unsigned _BitInt(4)) - 1 == 15);

  // promotion (or lack thereof)
  assert((unsigned _BitInt(4))15 + (unsigned _BitInt(4))1 == 0);
  assert((unsigned _BitInt(4))15 + (unsigned _BitInt(5))1 == 16);
  assert((unsigned _BitInt(4))15 + (signed _BitInt(5))1 == -16);
  assert((unsigned _BitInt(4))15 + 1 == 16);

  return 0;
}
