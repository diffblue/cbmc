#include <assert.h>
#include <string.h>

int main()
{
  int x;
  int *p = (char *)&x - 2;
  int y;
  memcpy(&y, p, sizeof(int));
  assert(0);
}
