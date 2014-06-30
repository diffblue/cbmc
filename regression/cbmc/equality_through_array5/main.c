#include <assert.h>

#define LIMIT 10

int pass_through_array (int x)
{
  int a[LIMIT];

  a[0] = x;
  for (int i = 1; i < LIMIT; ++i)
  {
    a[i] = a[i - 1];
  }

  return a[LIMIT - 1];
}

int main (void) {
  int x;

  assert(x == pass_through_array(x));

  return 1;
}

