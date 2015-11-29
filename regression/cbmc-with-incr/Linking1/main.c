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
  assert(a_struct.asd==0);
  
  f();
  
  assert(i==2);
  assert(a_struct.asd==123);
}
