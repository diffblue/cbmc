// to screw up the anon-counter

struct
{
  int abc;
};

#include "module.h"

anon_struct a_struct;

int i;

int main()
{
  assert(i==1);
  
  f();
  
  assert(i==2);
}
