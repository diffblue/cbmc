#include <assert.h>

int main(int argc, char *argv[])
{
  // Test if we can represent constant structs
  union union_struct {
    int a;
    int b;
  };

  union union_struct x = {0};
  x.a = 0;
  __CPROVER_assert(x.a == 0, "x.a==0");
  __CPROVER_assert(x.a == 1, "x.a==1");
  __CPROVER_assert(x.b == 0, "x.b==0");
  __CPROVER_assert(x.b == 1, "x.b==1");

  x.b = 1;
  __CPROVER_assert(x.a == 0, "x.a==0");
  __CPROVER_assert(x.a == 1, "x.a==1");
  __CPROVER_assert(x.b == 0, "x.b==0");
  __CPROVER_assert(x.b == 1, "x.b==1");

  return 0;
}
