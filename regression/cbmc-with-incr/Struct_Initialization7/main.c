#include <assert.h>

struct X
{
  union Y
  {
    int a, b, c;
  } y;
  
  int z;
};

int main()
{
  struct X x={ 1, 2 };
  
  assert(x.y.a==1);
  assert(x.z==2);
}
