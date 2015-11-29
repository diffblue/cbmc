#include <assert.h>

struct X
{
  struct Y
  {
    int z;
  } f [3];
  
  int g, h;

} foo = { .g=200, .f[1].z=100 };

struct Z {
  int a1, a2, a3, a4, a5;
} z =  { 10, .a3=30, 40 };

static int enable[32] = { 1, [30] = 2, 3 };

int main()
{
  assert(foo.f[0].z==0);
  assert(foo.f[1].z==100);
  assert(foo.f[2].z==0);
  assert(foo.g==200);
  assert(foo.h==0);

  assert(z.a1==10);
  assert(z.a2==0);
  assert(z.a3==30);
  assert(z.a4==40);
  assert(z.a5==0);
  
  assert(enable[0]==1);
  assert(enable[30]==2);
  assert(enable[31]==3);
}
