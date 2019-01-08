#include <assert.h>

double THREE = 3;

int main()
{
  // the rounding mode of the two '3' literals during
  // the conversion to double should match
  assert(THREE == 3);
}
