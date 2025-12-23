#include <assert.h>
#include <stdlib.h>

int main()
{
  int r = rand();
  assert(r >= 0);
  return 0;
}
