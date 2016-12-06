#include <assert.h>

#define LIMIT 4

int pass_through_array (int x)
{
  int a[LIMIT];

  a[0] = x;
  a[1] = a[0];
  a[2] = a[1];
  a[3] = a[2];

  return a[3];
}

int main (void) {
  int x;

  assert(x == pass_through_array(x));

  return 1;
}
