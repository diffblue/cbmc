#include <assert.h>

int nondet_int();

void main()
{
  int a = nondet_int();
  int b = nondet_int();
  int c = a +
#pragma CPROVER check disable "signed-overflow"
          (a + b);
#pragma CPROVER check pop

#pragma CPROVER check disable "signed-overflow"
  for(int i = 0; i < 10; ++i)
  {
    int temp = a + b;
#pragma CPROVER check pop
    int foo = temp + a;
    assert(foo > 2);
  }
}
