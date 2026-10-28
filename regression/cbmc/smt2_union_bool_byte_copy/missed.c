#include <assert.h>

union V
{
  _Bool b;
  unsigned char c;
};

union W
{
  int a;
  union V v;
};

unsigned char nondet_uchar(void);

int main(void)
{
  unsigned char x = nondet_uchar();
  __CPROVER_assume(x == 2);
  union V v;
  v.c = x;
  union W w;
  // copies the object representation of v
  w.v = v;
  // fails, as w.v.c is 2
  assert(w.v.c != 2);
  return 0;
}
