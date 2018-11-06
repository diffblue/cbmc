#include <assert.h>
#include <stdlib.h>

int main()
{
  __builtin_alloca();
  assert(0);
  return 0;
}
