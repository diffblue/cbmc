#include <assert.h>
#include <math.h>

int main()
{
  __builtin_isinff();
  assert(0);
  return 0;
}
