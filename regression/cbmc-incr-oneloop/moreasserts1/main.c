#include<assert.h>

extern int nondet_int();

int main()
{
  int z=nondet_int();
  int x=0;
  __CPROVER_assume(z<0 && z>-10);
  while(x<100) {
    assert(z<x);
    int y = nondet_int();
    __CPROVER_assume(y>0 && y<10);
    x=x+y;
    z=z-x;
    assert(x<150);
    if(z<-100) z=-z;
    assert(z<x);
  }
}
