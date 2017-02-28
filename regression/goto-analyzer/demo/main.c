#include <assert.h>


// To demonstrate run
// $ goto-analyzer main.c --variable --verify --pointers --structs
// Will show the asserts

// To see the pointer optimizations run
// $ goto-analyzer main.c --variable --simplify out.gb --pointers --structs
// $ goto-analyzer out.gb --show-goto-functions

void func(int unknwon);
int main()
{
  func(4);
}


// Pass in an unknown to show when we don't know what branch is taken

void func(int unknown)
{
  int i=0, j=2;
  if (i==0)
  {
    i++;
    j++;
  }

  // Knows we took if statement so can conclude assertion is true
  assert(j==3); // Verified

  int value=4;

  int * p2v = &value;
  int ** pp2v = &p2v;

  assert(*p2v==4);
  assert(**pp2v==4);

  value=10;

  // Tracks the value pointed to has changed
  assert(*p2v==10);
  assert(**pp2v==10);

  *p2v = 15;
  assert(value==15);
  assert(*p2v==15);
  assert(**pp2v==15);

  **pp2v = 20;
  assert(value==20);
  assert(*p2v==20);
  assert(**pp2v==20);

  int other = 5;
  p2v = &other;

  assert(*p2v==5);
  assert(**pp2v==5);

  if(unknown > 10)
  {
    p2v = &value;
  }
  else
  {
    p2v = &other;
  }

  assert(pp2v==&p2v); // success (even though p2v has changed)
  assert(*p2v==10); // unknown since we don't know anymore what p2v points to
  assert(**pp2v==10); // unknown

  // Running this through --simplify will yield:
  // yp = &x
  int x = 4;
  int * xp = &x;
  int * yp = xp;

  int ** ypp = &yp;
  **ypp = *yp;

  int i;
  int array[4];

  i = 0;
  array[i] = i;
  i = i+1;
  array[i] = i;
  i = i+1;
  array[i] = i;
  i = i+1;
  array[i] = i;
}
