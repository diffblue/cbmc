#include <assert.h>
int n=2, i, s, a = 0;
void main()
{
  i = 1;
  s = 1;
  if (a > 0)
    s = 0;
  while (i <= n) 
  {
    if (a > 0)
      s += 2;
    else
      s *= 2;
    i++;
  }
  assert(s>0);
}
