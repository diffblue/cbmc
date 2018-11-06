#include <assert.h>
#include <math.h>

int main()
{
  __builtin_huge_vall();
  assert(0);
  return 0;
}
