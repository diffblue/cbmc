#include <assert.h>

int main()
{
  int i=0, j=2;

  if (i==0) 
  {
    i++;
    j++;
  }
  assert(j!=3);
}
