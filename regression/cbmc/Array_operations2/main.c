#include <assert.h>

typedef struct my_struct
{
  char a;
  char b;
  char c[5];
} my_struct;

int main()
{
  my_struct arr[3] = {0};
  char *ptr = &(arr[1].c[2]);
  int offset;
  __CPROVER_assume(offset < 1 && offset > -1);
  void *ptr_plus = ptr + offset;
  char nondet[3];

  __CPROVER_array_replace(ptr_plus, &nondet[0]);

  // expected valid and proved
  assert(arr[0].a == 0);
  assert(arr[0].b == 0);
  assert(arr[0].c[0] == 0);
  assert(arr[0].c[1] == 0);
  assert(arr[0].c[2] == 0);
  assert(arr[0].c[3] == 0);
  assert(arr[0].c[4] == 0);

  assert(arr[1].a == 0);    // expected valid, falsified
  assert(arr[1].b == 0);    // expected valid, falsified
  assert(arr[1].c[0] == 0); // expected valid, falsified
  assert(arr[1].c[1] == 0); // expected valid, proved
  assert(arr[1].c[2] == 0); // expected falsifiable, proved
  assert(arr[1].c[3] == 0); // expected falsifiable, proved
  assert(arr[1].c[4] == 0); // expected falsifiable, proved

  // expected valid and proved
  assert(arr[2].a == 0);
  assert(arr[2].b == 0);
  assert(arr[2].c[0] == 0);
  assert(arr[2].c[1] == 0);
  assert(arr[2].c[2] == 0);
  assert(arr[2].c[3] == 0);
  assert(arr[2].c[4] == 0);

  return 0;
}
