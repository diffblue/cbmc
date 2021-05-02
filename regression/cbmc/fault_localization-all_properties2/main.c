#include <assert.h>

void main()
{
  int x, c;
  if(c)
    x = 0;
  else
    x++;
  assert(x == 0);
  assert(x == 0 || c == 0);
}
