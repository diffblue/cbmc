#include <assert.h>
int main()
{
  int a[2]={0,0};
  int i, y;

  if (a[0]==0)
    a[0]=1;

  assert(a[0]==2);

  return 0;
}

