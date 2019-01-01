#include <assert.h>

struct S
{
  unsigned int some_bit : 7;
};

int main()
{
  unsigned int i, j;
  double d;

  // double to integer and back
  i=100.0;
  d=i;
  j=d;
  assert(j==100);

  // double to bool and back
  _Bool b;
  b = 100.0;
  d = b;
  assert(d);

  // double to bit-field and back
  struct S s;
  s.some_bit = 100.0;
  d = s.some_bit;
  s.some_bit = d;
  assert(s.some_bit == 100);
}
