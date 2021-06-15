#include <assert.h>
#include <stdlib.h>

int main()
{
  unsigned int seed;
  int r = rand_r(&seed);
  assert(r >= 0);
  return 0;
}
