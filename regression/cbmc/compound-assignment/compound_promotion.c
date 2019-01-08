#include <assert.h>

int main()
{
  unsigned char x = 50;
  short y = -5;
  x /= y;
  assert(x == (unsigned char)-10);
  return 0;
}
