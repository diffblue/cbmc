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

  assert(0);
}
