#include <assert.h>
#include <stddef.h>

int main()
{
  int nondet;
  // Test reading from an array using a pointer
  int a[3] = {1, 2, 3};
  int *p = a;
  __CPROVER_assert(p == &a[0], "p==&a[0]");

  // Read through pointer
  __CPROVER_assert(*p == 1, "*p==1");

  // Read through offset pointer
  __CPROVER_assert(p[1] == 2, "p[1]==2");
  __CPROVER_assert(1 [p] == 2, "1[p]==2");

  __CPROVER_assert(*(p + 1) == 2, "*(p+1)==2");
  __CPROVER_assert(*(1 + p) == 2, "*(1+p)==2");

  // Test pointer arithmetic
  int *q = &a[1];
  __CPROVER_assert(q == p + 1, "q==p+1");
  __CPROVER_assert(*q == 2, "*q==2");
  __CPROVER_assert(*(q - 1) == 1, "*(q-1)==1");

  // Test pointer diffs
  ptrdiff_t x = 1;
  __CPROVER_assert(q - p == x, "q-p==x");

  // Test writing into an array using a pointer
  *q = 4;
  __CPROVER_assert(a[1] == 4, "a[1]==4");

  p[1] = 5;
  __CPROVER_assert(a[1] == 5, "a[1]==5");

  *(p + 1) = 6;
  __CPROVER_assert(a[1] == 6, "a[1]==6");

  *(1 + p) = 7;
  __CPROVER_assert(a[1] == 7, "a[1]==7");

  a[1] = 2;

  // We now explore pointers and indexes each with more than one possible value
  int *r = &a[1];
  int b[3] = {0, 0, 0};
  int *s = &b[1];
  int i = 1;
  if(nondet > 2)
  {
    r = &a[2];
    s = &b[2];
    i = 2;
  }

  // Test reading from an array using a pointer with more than one possible
  // value
  __CPROVER_assert(*r == 2, "*r==2");
  __CPROVER_assert(*r == 1, "*r==1");
  __CPROVER_assert(*s == 0, "*s==0");
  __CPROVER_assert(*s == 1, "*s==1");

  // Test pointer arithmetic with an unknown index
  int *t = &a[i];
  __CPROVER_assert(t == p + i, "t==p+i");

  // Test pointer diffs with an unknown index
  ptrdiff_t y = i;
  __CPROVER_assert(t - p == y, "t-p==y");

  // Test writing into an array using a pointer with an unknown index
  *r = 5;
  __CPROVER_assert(a[i] == 5, "a[i]==5");
  __CPROVER_assert(a[1] == 5, "a[1]==5");

  return 0;
}
