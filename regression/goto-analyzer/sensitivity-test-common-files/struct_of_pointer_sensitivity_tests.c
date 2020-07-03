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
  __CPROVER_assert(x.a == &a1, "x.a==&a1");
  __CPROVER_assert(x.a == &a2, "x.a==&a2");
  __CPROVER_assert(x.b == &b1, "x.b==&b1");
  __CPROVER_assert(x.b == &b2, "x.b==&b2");
  __CPROVER_assert(*x.a == 0, "*x.a==0");
  __CPROVER_assert(*x.a == 100, "*x.a==100");
  __CPROVER_assert(*x.b == 10.0f, "*x.b==10.0f");
  __CPROVER_assert(*x.b == 110.0f, "*x.b==110.0f");

  // Test merging when there is only one value on both paths
  if(argc>2)
  {
    x.a=&a1;
    x.b=&b1;
  }
  __CPROVER_assert(x.a == &a1, "x.a==&a1");
  __CPROVER_assert(x.a == &a2, "x.a==&a2");
  __CPROVER_assert(*x.a == 0, "*x.a==0");
  __CPROVER_assert(*x.a == 100, "*x.a==100");

  // Test merging when there is one value for a and two values for b, to test if
  // we are representing them separately
  if(argc>3)
  {
    x.a=&a1;
    x.b=&b2;
  }
  __CPROVER_assert(x.a == &a1, "x.a==&a1");
  __CPROVER_assert(x.b == &b2, "x.b==&b2");
  __CPROVER_assert(x.b == &b3, "x.b==&b3");
  __CPROVER_assert(*x.a == 0, "*x.a==0");
  __CPROVER_assert(*x.b == 11.0f, "*x.b==11.0f");
  __CPROVER_assert(*x.b == 12.0f, "*x.b==12.0f");

  // Test merging when there are two values for a and b
  if(argc>4)
  {
    x.a=&a2;
    x.b=&b3;
  }
  __CPROVER_assert(x.a == &a2, "x.a==&a2");
  __CPROVER_assert(x.a == &a3, "x.a==&a3");
  __CPROVER_assert(x.b == &b3, "x.b==&b3");
  __CPROVER_assert(x.b == &b4, "x.b==&b4");
  __CPROVER_assert(*x.a == 1, "*x.a==1");
  __CPROVER_assert(*x.a == 2, "*x.a==2");
  __CPROVER_assert(*x.b == 12.0f, "*x.b==12.0f");
  __CPROVER_assert(*x.b == 13.0f, "*x.b==13.0f");

  return 0;
}
