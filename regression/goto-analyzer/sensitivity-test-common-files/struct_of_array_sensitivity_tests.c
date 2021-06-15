#include <assert.h>

int main()
{
  int nondet;
  // Test how well we can represent structs
  struct int_array_float_array
  {
    int a[3];
    float b[3];
  };
  struct int_array_float_array x = {{0, 1, 2}, {3.0f, 4.0f, 5.0f}};
  x.a[0] = 0;
  x.a[1] = 1;
  x.a[2] = 2;
  x.b[0] = 3.0f;
  x.b[1] = 4.0f;
  x.b[2] = 5.0f;
  __CPROVER_assert(x.a[0] == 0, "x.a[0]==0");
  __CPROVER_assert(*(x.a + 0) == 0, "*(x.a+0)==0");
  __CPROVER_assert(*(0 + x.a) == 0, "*(0+x.a)==0");
  __CPROVER_assert(0 [x.a] == 0, "0[x.a]==0");

  // Test merging when there is only one value on both paths
  if(nondet > 2)
  {
    x.a[0] = 0;
  }
  __CPROVER_assert(x.a[0] == 0, "x.a[0]==0");
  __CPROVER_assert(x.a[1] == 1, "x.a[1]==1");
  __CPROVER_assert(x.b[0] == 3.0f, "x.b[0]==3.0f");

  // Test merging when there is one value for a and two values for b, to test if
  // we are representing them separately
  if(nondet > 3)
  {
    x.a[0] = 0;
    x.b[2] = 15.0f;
  }
  __CPROVER_assert(x.a[0] == 0, "x.a[0]==0");
  __CPROVER_assert(x.a[1] == 1, "x.a[1]==1");
  __CPROVER_assert(x.b[2] > 0.0f, "x.b[2]>0.0f");
  __CPROVER_assert(x.b[2] == 15.0f, "x.b[2]==15.0f");
  __CPROVER_assert(x.b[2] == 1.0f, "x.b[2]==1.0f");
  __CPROVER_assert(x.b[0] == 3.0f, "x.b[0]==3.0f");

  // Test merging when there are two values for a and b
  if(nondet > 4)
  {
    x.a[0] = 11;
    x.b[2] = 25.0f;
  }
  __CPROVER_assert(x.a[0] < 12, "x.a[0]<12");
  __CPROVER_assert(x.a[0] > 2, "x.a[0]>2");
  __CPROVER_assert(x.a[0] == 0, "x.a[0]==0");
  __CPROVER_assert(x.a[1] == 1, "x.a[1]==1");

  return 0;
}
