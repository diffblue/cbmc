#include <assert.h>
#include <math.h>

int main()
{
  __builtin_inff();
  assert(0);
  return 0;
}
