#include <assert.h>

int main()
{
  int *p, *q;
  long a, b;

  p = p + a;
  p = a + p + b;
  p = a + p;
  p = a + b + p;

  p = p - a;
  p = a + p - b;

  a = p - q;

  // mixing types: the C front-end will insert casts
  unsigned long long u;
  p = (p + a) + u;

  assert(0);
}
