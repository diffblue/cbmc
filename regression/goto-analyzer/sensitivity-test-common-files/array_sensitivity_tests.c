#include <assert.h>

int main()
{
  int nondet;
  // A uniform constant array
  int a[3] = {0, 0, 0};
  // A non-uniform constant array
  int b[3] = {1, 0, 0};

  // Test if we can represent uniform constant arrays
  __CPROVER_assert(a[1] == 0, "a[1]==0");
  __CPROVER_assert(a[1] == 1, "a[1]==1");

  // Test if we can represent constant arrays which aren't uniform
  __CPROVER_assert(b[1] == 0, "b[1]==0");
  __CPROVER_assert(b[1] == 1, "b[1]==1");

  // Test alternative syntax for accessing an array value
  __CPROVER_assert(*(b + 1) == 0, "*(b+1)==0");
  __CPROVER_assert(*(b + 1) == 1, "*(b+1)==1");
  __CPROVER_assert(*(1 + b) == 0, "*(1+b)==0");
  __CPROVER_assert(*(1 + b) == 1, "*(1+b)==1");
  __CPROVER_assert(1 [b] == 0, "1[b]==0");
  __CPROVER_assert(1 [b] == 1, "1[b]==1");

  // c and d are arrays whose values requiring merging paths in the CFG. For
  // c[0] there is only one possibility after merging and for d[0] there are
  // two.
  int c[3] = {0, 0, 0};
  int d[3] = {0, 0, 0};
  if(nondet > 2)
  {
    c[0] = 0;
    d[0] = 1;
  }

  // Test how well we can deal with merging for an array value
  __CPROVER_assert(c[0] == 0, "c[0]==0");
  __CPROVER_assert(c[0] == 1, "c[0]==1");
  __CPROVER_assert(d[0] == 0, "d[0]==0");
  __CPROVER_assert(d[0] == 2, "d[0]==2");
  __CPROVER_assert(d[1] == 0, "d[1]==0");

  // The variables i, j and k will be used as indexes into arrays of size 3.
  // They all require merging paths in the CFG. For i there is only one value on
  // both paths, which is a valid index. The rest can each take two different
  // values. For j both of these values are valid indexes. For k one is and one
  // isn't.
  int i = 0;
  int j = 0;
  int k = 0;
  if(nondet > 3)
  {
    i = 0;
    j = 1;
    k = 100;
  }

  // Test how well we can deal with merging for an index on a uniform array
  __CPROVER_assert(a[i] == 0, "a[i]==0");
  __CPROVER_assert(a[i] == 1, "a[i]==1");
  __CPROVER_assert(a[j] == 0, "a[j]==0");
  __CPROVER_assert(a[j] == 1, "a[j]==1");

  // Test how well we can deal with merging for an index on a non-uniform array
  __CPROVER_assert(b[i] == 1, "b[i]==1");
  __CPROVER_assert(b[i] == 0, "b[i]==0");
  __CPROVER_assert(b[j] == 0, "b[j]==0");
  __CPROVER_assert(b[j] == 1, "b[j]==1");

  // Test how we deal with reading off the end of an array
  __CPROVER_assert(a[100] == 0, "a[100]==0");

  // Test how we deal with writing off the end of an array
  a[100] = 1;
  __CPROVER_assert(b[1] == 0, "b[1]==0");

  // Test how we deal with merging for an index with one possible value when
  // writing to an array
  int ei[3] = {0, 0, 0};
  ei[i] = 1;
  __CPROVER_assert(ei[0] == 1, "ei[0]==1");
  __CPROVER_assert(ei[0] == 0, "ei[0]==0");
  __CPROVER_assert(ei[2] == 0, "ei[2]==0");
  __CPROVER_assert(ei[2] == 1, "ei[2]==1");

  // Test how we deal with merging for an index with two possible values when
  // writing to an array
  int ej[3] = {0, 0, 0};
  ej[j] = 1;
  __CPROVER_assert(ej[0] == 0, "ej[0]==0");
  __CPROVER_assert(ej[2] == 0, "ej[2]==0");

  // Test how we deal with merging for an index with two possible values when
  // it means writing to an array element that may be out of bounds
  int ek[3] = {0, 0, 0};
  ek[k] = 1;
  __CPROVER_assert(ek[0] == 0, "ek[0]==0");

  return 0;
}
