#include <assert.h>

int f()
{
  return 1;
}

int main()
{
  int i;
  
  int x = ({f();});
  assert(x==1);

  int y = ({ i = f(); });
  assert(y==1);
  assert(i==1);

  // ordering of side-effects in there
  int z = ({ i=1; i++; });
  assert(z==1);
  assert(i==2);
  
  // same at top level
  ({ i=1; i++; });
  assert(i==2);

  return 0;
}
