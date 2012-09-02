#include <assert.h>

int a[10][4];
int *p;

int main()
{
  assert(sizeof(a[0])==sizeof(int)*4);

  p=a[9];
  assert(p==a[0]+9*4);
  
  *p=10;
  assert(a[9][0]==10);

  p++;  
  *p=20;
  assert(a[9][1]==20);

  // we can wrap around
  p=a[0]+4;
  *p=30;
  assert(a[1][0]==30);
}
