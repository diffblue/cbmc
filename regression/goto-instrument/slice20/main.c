#include <assert.h>

void recursion(_Bool rec, int *p)
{
  int some_local, other_local;

  if(rec)
  {
    some_local=2;
    other_local=30;
    rec=1;
    *p=20; // overwrites other_local in previous frame
    assert(other_local==30);
  }
  else
  {
    some_local=1;
    other_local=10;
    recursion(1, &other_local);
    assert(!rec);
    assert(some_local==1);
    assert(other_local==20);
  }
}

int main()
{
  recursion(0, 0);
}
