#include <assert.h>

union U
{
  short a;
  int b;
  char c[4];
};

int main()
{
  if(sizeof(short)!=2 ||
     sizeof(int)!=4)
    return 0;

  union U u;
  u.b=0x04030201;

  assert(u.a==0x0403);
  assert(u.c[0]==0x04);
  assert(u.c[1]==0x03);
  assert(u.c[2]==0x02);
  assert(u.c[3]==0x01);

  return 0;
}
