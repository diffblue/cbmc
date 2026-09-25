#include <assert.h>
#include <math.h>

int main()
{
  __builtin_finitel();
  assert(0);
  return 0;
}
