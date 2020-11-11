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
  int i = 0, j = 2;
  if(i == 0)
  {
    i++;
    j++;
  }

  // Knows we took if statement so can conclude assertion is true
  __CPROVER_assert(j == 3, "j==3"); // Verified

  int value = 4;

  int *p2v = &value;
  int **pp2v = &p2v;

  __CPROVER_assert(*p2v == 4, "*p2v==4");
  __CPROVER_assert(**pp2v == 4, "**pp2v==4");

  value = 10;

  // Tracks the value pointed to has changed
  __CPROVER_assert(*p2v == 10, "*p2v==10");
  __CPROVER_assert(**pp2v == 10, "**pp2v==10");

  *p2v = 15;
  __CPROVER_assert(value == 15, "value==15");
  __CPROVER_assert(*p2v == 15, "*p2v==15");
  __CPROVER_assert(**pp2v == 15, "**pp2v==15");

  **pp2v = 20;
  __CPROVER_assert(value == 20, "value==20");
  __CPROVER_assert(*p2v == 20, "*p2v==20");
  __CPROVER_assert(**pp2v == 20, "**pp2v==20");

  int other = 5;
  p2v = &other;

  __CPROVER_assert(*p2v == 5, "*p2v==5");
  __CPROVER_assert(**pp2v == 5, "**pp2v==5");

  if(unknown > 10)
  {
    p2v = &value;
  }
  else
  {
    p2v = &other;
  }

  __CPROVER_assert(
    pp2v == &p2v, "pp2v==&p2v"); // success (even though p2v has changed)
  __CPROVER_assert(
    *p2v == 10,
    "*p2v==10"); // unknown since we don't know anymore what p2v points to
  __CPROVER_assert(**pp2v == 10, "**pp2v==10"); // unknown

  // Running this through --simplify will yield:
  // yp = &x
  int x = 4;
  int *xp = &x;
  int *yp = xp;

  int **ypp = &yp;
  **ypp = *yp;

  int array[4] = {0, 1, 2, 3};

  __CPROVER_assert(array[0] == 0, "array[0] == 0"); // Success
  __CPROVER_assert(array[3] == 3, "array[3] == 3"); // Success

  if(unknown > 10)
  {
    array[0] = 4;
    array[1] = 1;
    array[2] = 5;
  }
  else
  {
    array[0] = 4;
    array[2] = 10;
  }

  __CPROVER_assert(array[0] == 4, "array[0] == 4"); // Success
  __CPROVER_assert(array[1] == 1, "array[1] == 1"); // Success
  __CPROVER_assert(array[2] == 5, "array[2] == 5"); // Unknown
  __CPROVER_assert(array[3] == 3, "array[3] == 3"); // Success

  typedef struct
  {
    int a;
    int b;
  } struct_t;

  struct_t s;
  s.a = 1;

  __CPROVER_assert(s.a == 1, "s.a == 1");
  __CPROVER_assert(s.a == 2, "s.a == 2");
}
