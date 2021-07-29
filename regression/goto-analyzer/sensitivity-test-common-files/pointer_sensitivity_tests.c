#include <assert.h>

int main(int argc, char *argv[])
{
  // Test how well we can represent pointers
  // Basic use of addresses
  int a=0;
  int b=0;
  int c=0;
  int *x=&a;
  int *x2=&a;
  int *y=&b;
  __CPROVER_assert(x == &a, "x==&a");
  __CPROVER_assert(x == &b, "x==&b");
  __CPROVER_assert(x == x2, "x==x2");
  __CPROVER_assert(x == y, "x==y");

  // Reading from a dereferenced pointer
  __CPROVER_assert(*x == 0, "*x==0");
  __CPROVER_assert(*x == 1, "*x==1");

  // Modify the referenced value and access it through the pointer again
  a=1;
  __CPROVER_assert(*x == 1, "*x==1");
  __CPROVER_assert(*x == 0, "*x==0");

  // Writing to a dereferenced pointer
  *x=2;
  __CPROVER_assert(a == 2, "a==2");
  __CPROVER_assert(a == 0, "a==0");

  // Conditionally reassign the pointer, but to the same value
  if(argc>2)
  {
    x=&a;
  }
  __CPROVER_assert(x == &a, "x==&a");

  // Conditionally reassign the pointer, to a different value this time
  if(argc>3)
  {
    x=&b;
  }
  else
  {
    x=&c;
  }
  __CPROVER_assert(*x == 0, "*x==0");
  __CPROVER_assert(x == &a, "x==&a");
  __CPROVER_assert(x == &b, "x==&b");
  __CPROVER_assert(x == &c, "x==&c");

  return 0;
}
