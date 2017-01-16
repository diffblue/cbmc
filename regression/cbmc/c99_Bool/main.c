#include <assert.h>

void foo(_Bool y)
{
  int x;
  if(y) 
  {  
    x=(int)y;
    assert(x==1);
  }
}
