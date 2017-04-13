#include <assert.h>

int main(int argc, char *argv[])
{
  // Test how well we can represent structs of pointers
  int a1=0;
  int a2=1;
  int a3=2;
  float b1=10.0f;
  float b2=11.0f;
  float b3=12.0f;
  float b4=13.0f;
  struct int_float
  {
    int *a;
    float *b;
  };
  struct int_float x;
  x.a=&a1;
  x.b=&b1;
  assert(x.a==&a1);
  assert(x.a==&a2);
  assert(x.b==&b1);
  assert(x.b==&b2);
  assert(*x.a==0);
  assert(*x.a==100);
  assert(*x.b==10.0f);
  assert(*x.b==110.0f);

  // Test merging when there is only one value on both paths
  if(argc>2)
  {
    x.a=&a1;
    x.b=&b1;
  }
  assert(x.a==&a1);
  assert(x.a==&a2);
  assert(*x.a==0);
  assert(*x.a==100);

  // Test merging when there is one value for a and two values for b, to test if
  // we are representing them separately
  if(argc>3)
  {
    x.a=&a1;
    x.b=&b2;
  }
  assert(x.a==&a1);
  assert(x.b==&b2);
  assert(x.b==&b3);
  assert(*x.a==0);
  assert(*x.b==11.0f);
  assert(*x.b==12.0f);

  // Test merging when there are two values for a and b
  if(argc>4)
  {
    x.a=&a2;
    x.b=&b3;
  }
  assert(x.a==&a2);
  assert(x.a==&a3);
  assert(x.b==&b3);
  assert(x.b==&b4);
  assert(*x.a==1);
  assert(*x.a==2);
  assert(*x.b==12.0f);
  assert(*x.b==13.0f);

  return 0;
}
