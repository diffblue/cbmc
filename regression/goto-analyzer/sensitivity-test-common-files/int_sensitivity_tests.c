#include <assert.h>

int main(int argc, char *argv[])
{
  // Test how well we can represent ints, and also that the transformers are
  // working correctly.
  int x=0;
  int y=0;
  if(argc>2)
  {
    y=1;
  }
  __CPROVER_assert(x == 0, "x==0");
  __CPROVER_assert(x == 1, "x==1");
  __CPROVER_assert(x == y, "x==y");

  __CPROVER_assert(x < 1, "x<1");
  __CPROVER_assert(x < -1, "x<-1");
  __CPROVER_assert(x < y, "x<y");

  __CPROVER_assert(x > -1, "x>-1");
  __CPROVER_assert(x > 1, "x>1");
  __CPROVER_assert(x > y, "x>y");

  __CPROVER_assert(x != 1, "x!=1");
  __CPROVER_assert(x != 0, "x!=0");
  __CPROVER_assert(x != y, "x!=y");

  __CPROVER_assert(!(x == 1), "!(x==1)");
  __CPROVER_assert(!(x == 0), "!(x==0)");
  __CPROVER_assert(!(x == y), "!(x==y)");

  // Test how well we can represent an int when it has more than one possible
  // value
  __CPROVER_assert(y < 2, "y<2");
  __CPROVER_assert(y > 2, "y>2");
  __CPROVER_assert(y == 1, "y==1");

  // Try copying a variable and then modifying the original
  int z=x;
  x=10;
  __CPROVER_assert(z == 0, "z==0");
  __CPROVER_assert(z == 10, "z==10");

  // Test how we treat assertions in unreachable code
  x=0;
  if(0)
  {
    __CPROVER_assert(x == 0, "x==0");
    __CPROVER_assert(x == 1, "x==1");
    __CPROVER_assert(y == 0, "y==0");
  }

  // Try merging two states with multiple variables

  int a1 = 0;
  int a2 = 0;
  int a3 = 0;
  int a4 = 0;
  int a5 = 0;
  if(argc > 2)
  {
    a1 = argc;
    a2 = argc;
    a3 = argc;
    // all three variables are now top in this branch
  }

  // all three asserts are unverifiable
  __CPROVER_assert(a1 == 0, "a1==0");
  __CPROVER_assert(a2 == 0, "a2==0");
  __CPROVER_assert(a3 == 0, "a3==0");
  __CPROVER_assert(a4 == 0, "a4==0");
  __CPROVER_assert(a5 == 0, "a5==0");

  return 0;
}
