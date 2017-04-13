#include <assert.h>

int main(int argc, char *argv[])
{
  // Test how well we can represent arrays of pointers
  int a0=0;
  int a1=1;
  int a2=2;
  int a3=3;
  int b0=10;
  int b1=11;
  int b2=12;
  int b3=13;
  int c0=20;
  int c1=21;
  int c2=22;
  int c3=23;
  int d0=30;
  int d1=31;
  int d2=32;
  int d3=33;
  // A uniform constant array
  int *a[3]={&a0, &a0, &a0};
  // A non-uniform constant array
  int *b[3]={&b0, &b1, &b2};

  // Test if we can represent uniform constant arrays
  assert(a[1]==&a0);
  assert(a[1]==&a3);
  assert(*a[1]==0);
  assert(*a[1]==3);

  // Test if we can represent constant arrays which aren't uniform
  assert(b[1]==&b1);
  assert(b[1]==&b3);
  assert(*b[1]==11);
  assert(*b[1]==13);

  // Test alternative syntax for accessing an array value
  assert(*(b+1)==&b1);
  assert(*(b+1)==&b3);
  assert(*(1+b)==&b1);
  assert(*(1+b)==&b3);
  assert(1[b]==&b1);
  assert(1[b]==&b3);
  assert(**(b+1)==11);
  assert(**(b+1)==13);
  assert(**(1+b)==11);
  assert(**(1+b)==13);
  assert(*1[b]==11);
  assert(*1[b]==13);

  // c and d are arrays whose values requiring merging paths in the CFG. For
  // c[0] there is only one possibility after merging and for d[0] there are
  // two.
  int *c[3]={&c0, &c1, &c2};
  int *d[3]={&d0, &d1, &d2};
  if(argc>2)
  {
    c[0]=&c3;
    d[0]=&d3;
  }

  // Test how well we can deal with merging for an array value
  assert(c[0]==&c0);
  assert(c[0]==&c3);
  assert(d[0]==&d0);
  assert(d[0]==&d3);
  assert(*c[0]==20);
  assert(*c[0]==23);
  assert(*d[0]==30);
  assert(*d[0]==33);

  // The variables i, j and k will be used as indexes into arrays of size 3.
  // They all require merging paths in the CFG. For i there is only one value on
  // both paths, which is a valid index. The rest can each take two different
  // values. For j both of these values are valid indexes. For k one is and one
  // isn't.
  int i=0;
  int j=0;
  int k=0;
  if(argc>3)
  {
    i=0;
    j=1;
    k=100;
  }

  // Test how well we can deal with merging for an index on a uniform array
  assert(a[i]==&a0);
  assert(a[i]==&a3);
  assert(a[j]==&a0);
  assert(a[j]==&a3);
  assert(*a[i]==0);
  assert(*a[i]==3);
  assert(*a[j]==0);
  assert(*a[j]==3);

  // Test how well we can deal with merging for an index on a non-uniform array
  assert(b[i]==&b0);
  assert(b[i]==&b1);
  assert(b[j]==&b0);
  assert(b[j]==&b3);
  assert(*b[i]==10);
  assert(*b[i]==11);
  assert(*b[j]==10);
  assert(*b[j]==13);

  // Test how we deal with reading off the end of an array
  assert(a[100]==&a2);
  assert(*a[100]==2);

  // Test how we deal with writing off the end of an array
  a[100]=&a2;
  assert(b[1]==&b1);
  assert(*b[1]==11);

  // Test how we deal with merging for an index with one possible value when
  // writing to an array
  int ei0=40;
  int ei1=41;
  int *ei[3]={&ei0, &ei0, &ei0};
  ei[i]=&ei1;
  assert(ei[0]==&ei1);
  assert(ei[0]==&ei0);
  assert(ei[2]==&ei0);
  assert(ei[2]==&ei1);
  assert(*ei[0]==41);
  assert(*ei[0]==40);
  assert(*ei[2]==40);
  assert(*ei[2]==41);

  // Test how we deal with merging for an index with two possible values when
  // writing to an array
  int ej0=50;
  int ej1=51;
  int *ej[3]={&ej0, &ej0, &ej0};
  ej[j]=&ej1;
  assert(ej[0]==&ej0);
  assert(ej[2]==&ej0);
  assert(ej[2]==&ej1);
  assert(*ej[0]==50);
  assert(*ej[2]==50);
  assert(*ej[2]==51);

  // Test how we deal with merging for an index with two possible values when
  // it means writing to an array element that may be out of bounds
  int ek0=60;
  int ek1=61;
  int *ek[3]={&ek0, &ek0, &ek0};
  ek[k]=&ek1;
  assert(ek[0]==&ek0);
  assert(*ek[0]==60);

  return 0;
}
