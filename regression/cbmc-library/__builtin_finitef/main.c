#include <assert.h>
#include <math.h>

int main()
{
  __builtin_finitef();
  assert(0);
  return 0;
}
