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
  assert(x==&a);
  assert(x==&b);
  assert(x==x2);
  assert(x==y);

  // Reading from a dereferenced pointer
  assert(*x==0);
  assert(*x==1);

  // Modify the referenced value and access it through the pointer again
  a=1;
  assert(*x==1);
  assert(*x==0);

  // Writing to a dereferenced pointer
  *x=2;
  assert(a==2);
  assert(a==0);

  // Conditionally reassign the pointer, but to the same value
  if(argc>2)
  {
    x=&a;
  }
  assert(x==&a);

  // Conditionally reassign the pointer, to a different value this time
  if(argc>3)
  {
    x=&b;
  }
  else
  {
    x=&c;
  }
  assert(*x==0);
  assert(x==&a);
  assert(x==&b);

  return 0;
}
