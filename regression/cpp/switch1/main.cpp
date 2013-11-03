#include <assert.h>

int main()
{
  int i;
  
  switch(i)
  {
  case 0: assert(i==0);
          /* fall through */
  case 1: assert(i==0 || i==1);
          break;

  default:
    assert(i!=0 && i!=1);
  }
  
  int z=0;
  
  // a declaration is ok here
  #if 0
  switch(int z=123)
  {
  case 123: assert(z==123); break;
  default: assert(0);
  }
  #endif
  
  assert(z==0);
}
