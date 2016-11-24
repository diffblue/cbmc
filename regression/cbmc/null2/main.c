#include <assert.h>

int main()
{
  long tmp;
  if((void*)tmp)
  {
    tmp=1;
  }
  assert(tmp!=0);

  return 0;
}
