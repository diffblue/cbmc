#include <assert.h>
#include <stddef.h>

int main(int argc, char *argv[])
{
  // Test reading from an array using a pointer
  int a[3]={1, 2, 3};
  int *p=a;
  assert(p==&a[0]);
  assert(*p==1);

  // Test pointer arithmetic
  int *q=&a[1];
  assert(q==p+1);
  assert(*q==2);

  // Test pointer diffs
  ptrdiff_t x=1;
  assert(q-p==x);

  // Test writing into an array using a pointer
  *q=4;
  assert(a[1]==4);

  q[1]=5;
  assert(a[1]==5);

  a[1]=2;

  // We now explore pointers and indexes each with more than one possible value
  int *r=&a[1];
  int b[3]={0, 0, 0};
  int *s=&b[1];
  int i=1;
  if (argc>2)
  {
    r=&a[2];
    s=&b[2];
    i=2;
  }

  // Test reading from an array using a pointer with more than one possible
  // value
  assert(*r==2);
  assert(*r==1);
  assert(*s==0);
  assert(*s==1);

  // Test pointer arithmetic with an unknown index
  int *t=&a[i];
  assert(t==p+i);

  // Test pointer diffs with an unknown index
  ptrdiff_t y=i;
  assert(t-p==y);

  // Test writing into an array using a pointer with an unknown index
  *r=5;
  assert(a[i]==5);
  assert(a[1]==5);

  return 0;
}
