#if 1
typedef unsigned uint;
#endif

#include "masc.h"
#include <cassert>

mv<int,char> init_mv()
{
  char z=1;
  mv<int,char> m(0,z);
  return m;
}

void test_mv()
{
  mv<int,char> m = init_mv();

  int x;
  char y;
  m.assign(x,y);

  assert(x==0);
  assert(y==1);
}

#define SIZE 5

array<SIZE,int> init_array()
{
  array<SIZE,int> a;
  for(int i=0;i<SIZE;i++)
    a.elt[i] = i*i;
  return a;
}

void test_array()
{
  array<SIZE,int> a = init_array();
  assert(a.elt[SIZE-1]==(SIZE-1)*(SIZE-1));
}

int main (int argc, char *argv[])
{
  test_mv();
  test_array();
  return 0;
}
