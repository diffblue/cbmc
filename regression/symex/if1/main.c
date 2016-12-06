#include <assert.h>

int main()
{
  int i;

  if(i==1)
    assert(i==1);
  else
    assert(i!=1);

  assert(i!=1);
}
