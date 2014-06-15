#include <assert.h>

void f1()
{
  // goes into global name space!
  extern int i;
  assert(i==1);
}

int i;

int main()
{
  i=1;
  f1();
}
