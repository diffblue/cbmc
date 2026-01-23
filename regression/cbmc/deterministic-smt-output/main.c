#include <assert.h>

int main()
{
  int x;
  int y;
  int z = x + y;
  assert(z == x + y);
  return 0;
}
