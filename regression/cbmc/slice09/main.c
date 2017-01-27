#include <assert.h>
int n=2;
void main()
{
  int i=1;
  while (i <= n) 
    i++;
  assert(i>=0);
}
