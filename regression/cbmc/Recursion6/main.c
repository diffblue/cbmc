#include <assert.h>

void recursion(_Bool rec)
{
  int some_local;

  if(rec)
  {
    some_local=2;
    rec=1;
  }
  else
  {
    some_local=1;
    recursion(1);
    assert(!rec);
    assert(some_local==1);
  }
}

int main()
{
  recursion(0);
}
