#include <assert.h>

void f1()
{
  // goes into global name space!
  extern int i;
  assert(i==1);
  
  // and might have an incomplete type
  extern struct unknown_tag some_struct;
  extern char some_array[];
  typedef int some_incomplete_type[];
  extern some_incomplete_type some_other;
}

int i;

int main()
{
  i=1;
  f1();
}
