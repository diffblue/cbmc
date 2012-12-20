#include "module.h"

extern int i;

int main()
{
  assert(i==1);
  
  T t;
  t.f();
  
  assert(i==2);
}
