#include <assert.h>

int main(int argc, char *argv[])
{
  // Test how well we can represent structs of structs
  struct int_float
  {
    int a;
    float b;
  };
  struct two_int_floats
  {
    struct int_float s1;
    struct int_float s2;
  };
  struct two_int_floats x;
  x.s1.a=0;
  x.s1.b=1.0;
  x.s2.a=2;
  x.s2.b=3.0f;
  __CPROVER_assert(x.s1.a == 0, "x.s1.a==0");
  __CPROVER_assert(x.s2.b == 3.0f, "x.s2.b==3.0f");

  // Test merging when there is only one value on both paths
  if(argc>2)
  {
    x.s1.a=0;
  }
  __CPROVER_assert(x.s1.a == 0, "x.s1.a==0");
  __CPROVER_assert(x.s1.a == 10, "x.s1.a==10");

  // Test merging when there is one value for s1 and two values for s2, to test
  // if we are representing them separately
  if(argc>3)
  {
    x.s1.b=1.0f;
    x.s2.b=13.0f;
  }
  __CPROVER_assert(x.s1.b == 1.0f, "x.s1.b==1.0f");
  __CPROVER_assert(x.s2.b == 3.0f, "x.s2.b==3.0f");
  __CPROVER_assert(x.s2.b == 0.0f, "x.s2.b==0.0f");

  // Test merging when there are two values for s1 and s2
  if(argc>4)
  {
    x.s1.a=20;
    x.s2.a=22;
  }
  __CPROVER_assert(x.s1.a == 20, "x.s1.a==20");
  __CPROVER_assert(x.s1.a < 30, "x.s1.a<30");
  __CPROVER_assert(x.s2.a == 22, "x.s2.a==22");
  __CPROVER_assert(x.s2.a < 30, "x.s2.a<30");

  return 0;
}
