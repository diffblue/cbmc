#include <assert.h>

struct S
{
  short a;
  short b;
};

int main()
{
  if(sizeof(short)!=2 ||
     sizeof(int)!=4 ||
     sizeof(struct S)!=4)
    return 0;

  struct S s;
  s.a=0x0201;
  s.b=0x0403;
  assert(*(int*)&s==0x02010403);

  return 0;
}
