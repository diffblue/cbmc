#include <assert.h>

_Bool glob, result;

_Bool my_f()
{
  glob=1;
  return 0;
}

int main()
{
  // side-effect in ?:
  glob=0;  
  result=glob?1:my_f();  
  assert(result==0);
  
  // side-effect in ||
  glob=0;
  result=glob||my_f();
  assert(result==0);

  // side-effect deep down
  glob=0;
  result=glob||(0+my_f());
  assert(result==0);
  
  // another variant of this
  int r, c=1;  
  r=c?(c=0, 10):20;
  assert(c==0 && r==10);
}
