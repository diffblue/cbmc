#include <assert.h>

int main(void)
{
  enum A { zero, one, two, three } a = two, b = one, c = three;

  a <<= b;
  assert(a==4);

  c += b;
  assert(c==4);

  enum E { fortytwo=42 } e = fortytwo;
  double res;
  res = -42.0 + (double) e;
  assert ((res >= -0.000005) && (res <= 0.000005));

  return 0;
}
