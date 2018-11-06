#include <assert.h>
#include <math.h>

int main()
{
  __builtin_nanf();
  assert(0);
  return 0;
}
