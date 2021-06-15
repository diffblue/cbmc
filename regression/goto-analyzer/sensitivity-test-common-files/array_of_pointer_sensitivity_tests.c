#include <assert.h>

int main()
{
  int nondet;
  // Test how well we can represent arrays of pointers
  int a0 = 0;
  int a1 = 1;
  int a2 = 2;
  int a3 = 3;
  int b0 = 10;
  int b1 = 11;
  int b2 = 12;
  int b3 = 13;
  int c0 = 20;
  int c1 = 21;
  int c2 = 22;
  int c3 = 23;
  int d0 = 30;
  int d1 = 31;
  int d2 = 32;
  int d3 = 33;
  // A uniform constant array
  int *a[3] = {&a0, &a0, &a0};
  // A non-uniform constant array
  int *b[3] = {&b0, &b1, &b2};

  // Test if we can represent uniform constant arrays
  __CPROVER_assert(a[1] == &a0, "a[1]==&a0");
  __CPROVER_assert(a[1] == &a3, "a[1]==&a3");
  __CPROVER_assert(*a[1] == 0, "*a[1]==0");
  __CPROVER_assert(*a[1] == 3, "*a[1]==3");

  // Test if we can represent constant arrays which aren't uniform
  __CPROVER_assert(b[1] == &b1, "b[1]==&b1");
  __CPROVER_assert(b[1] == &b3, "b[1]==&b3");
  __CPROVER_assert(*b[1] == 11, "*b[1]==11");
  __CPROVER_assert(*b[1] == 13, "*b[1]==13");

  // Test alternative syntax for accessing an array value
  __CPROVER_assert(*(b + 1) == &b1, "*(b+1)==&b1");
  __CPROVER_assert(*(b + 1) == &b3, "*(b+1)==&b3");
  __CPROVER_assert(*(1 + b) == &b1, "*(1+b)==&b1");
  __CPROVER_assert(*(1 + b) == &b3, "*(1+b)==&b3");
  __CPROVER_assert(1 [b] == &b1, "1[b]==&b1");
  __CPROVER_assert(1 [b] == &b3, "1[b]==&b3");
  __CPROVER_assert(**(b + 1) == 11, "**(b+1)==11");
  __CPROVER_assert(**(b + 1) == 13, "**(b+1)==13");
  __CPROVER_assert(**(1 + b) == 11, "**(1+b)==11");
  __CPROVER_assert(**(1 + b) == 13, "**(1+b)==13");
  __CPROVER_assert(*1 [b] == 11, "*1[b]==11");
  __CPROVER_assert(*1 [b] == 13, "*1[b]==13");

  // c and d are arrays whose values requiring merging paths in the CFG. For
  // c[0] there is only one possibility after merging and for d[0] there are
  // two.
  int *c[3] = {&c0, &c1, &c2};
  int *d[3] = {&d0, &d1, &d2};
  if(nondet > 2)
  {
    c[0] = &c3;
    d[0] = &d3;
  }

  // Test how well we can deal with merging for an array value
  __CPROVER_assert(c[0] == &c0, "c[0]==&c0");
  __CPROVER_assert(c[0] == &c3, "c[0]==&c3");
  __CPROVER_assert(d[0] == &d0, "d[0]==&d0");
  __CPROVER_assert(d[0] == &d3, "d[0]==&d3");
  __CPROVER_assert(*c[0] == 20, "*c[0]==20");
  __CPROVER_assert(*c[0] == 23, "*c[0]==23");
  __CPROVER_assert(*d[0] == 30, "*d[0]==30");
  __CPROVER_assert(*d[0] == 33, "*d[0]==33");

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
  __CPROVER_assert(a[i] == &a0, "a[i]==&a0");
  __CPROVER_assert(a[i] == &a3, "a[i]==&a3");
  __CPROVER_assert(a[j] == &a0, "a[j]==&a0");
  __CPROVER_assert(a[j] == &a3, "a[j]==&a3");
  __CPROVER_assert(*a[i] == 0, "*a[i]==0");
  __CPROVER_assert(*a[i] == 3, "*a[i]==3");
  __CPROVER_assert(*a[j] == 0, "*a[j]==0");
  __CPROVER_assert(*a[j] == 3, "*a[j]==3");

  // Test how well we can deal with merging for an index on a non-uniform array
  __CPROVER_assert(b[i] == &b0, "b[i]==&b0");
  __CPROVER_assert(b[i] == &b1, "b[i]==&b1");
  __CPROVER_assert(b[j] == &b0, "b[j]==&b0");
  __CPROVER_assert(b[j] == &b3, "b[j]==&b3");
  __CPROVER_assert(*b[i] == 10, "*b[i]==10");
  __CPROVER_assert(*b[i] == 11, "*b[i]==11");
  __CPROVER_assert(*b[j] == 10, "*b[j]==10");
  __CPROVER_assert(*b[j] == 13, "*b[j]==13");

  // Test how we deal with reading off the end of an array
  __CPROVER_assert(a[100] == &a2, "a[100]==&a2");
  __CPROVER_assert(*a[100] == 2, "*a[100]==2");

  // Test how we deal with writing off the end of an array
  a[100] = &a2;
  __CPROVER_assert(b[1] == &b1, "b[1]==&b1");
  __CPROVER_assert(*b[1] == 11, "*b[1]==11");

  // Test how we deal with merging for an index with one possible value when
  // writing to an array
  int ei0 = 40;
  int ei1 = 41;
  int *ei[3] = {&ei0, &ei0, &ei0};
  ei[i] = &ei1;
  __CPROVER_assert(ei[0] == &ei1, "ei[0]==&ei1");
  __CPROVER_assert(ei[0] == &ei0, "ei[0]==&ei0");
  __CPROVER_assert(ei[2] == &ei0, "ei[2]==&ei0");
  __CPROVER_assert(ei[2] == &ei1, "ei[2]==&ei1");
  __CPROVER_assert(*ei[0] == 41, "*ei[0]==41");
  __CPROVER_assert(*ei[0] == 40, "*ei[0]==40");
  __CPROVER_assert(*ei[2] == 40, "*ei[2]==40");
  __CPROVER_assert(*ei[2] == 41, "*ei[2]==41");

  // Test how we deal with merging for an index with two possible values when
  // writing to an array
  int ej0 = 50;
  int ej1 = 51;
  int *ej[3] = {&ej0, &ej0, &ej0};
  ej[j] = &ej1;
  __CPROVER_assert(ej[0] == &ej0, "ej[0]==&ej0");
  __CPROVER_assert(ej[2] == &ej0, "ej[2]==&ej0");
  __CPROVER_assert(ej[2] == &ej1, "ej[2]==&ej1");
  __CPROVER_assert(*ej[0] == 50, "*ej[0]==50");
  __CPROVER_assert(*ej[2] == 50, "*ej[2]==50");
  __CPROVER_assert(*ej[2] == 51, "*ej[2]==51");

  // Test how we deal with merging for an index with two possible values when
  // it means writing to an array element that may be out of bounds
  int ek0 = 60;
  int ek1 = 61;
  int *ek[3] = {&ek0, &ek0, &ek0};
  ek[k] = &ek1;
  __CPROVER_assert(ek[0] == &ek0, "ek[0]==&ek0");
  __CPROVER_assert(*ek[0] == 60, "*ek[0]==60");

  // Test writing to an unknown index (i.e. a merging write of the pointer)
  int x = 4;
  int y = 5;
  int *ps[2] = {&x, &y};
  int i;
  if(nondet > 2)
  {
    i = 0;
  }
  else
  {
    i = 1;
  }
  *(ps[i]) = 4;

  __CPROVER_assert(*ps[0] == 4, "*ps[0]==4");
  __CPROVER_assert(*ps[1] == 4, "*ps[1]==4");
  __CPROVER_assert(x == 4, "x==4");
  __CPROVER_assert(y == 4, "y==4");

  return 0;
}
