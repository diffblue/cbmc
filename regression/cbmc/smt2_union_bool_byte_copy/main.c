#include <assert.h>

union V
{
  _Bool b;
  unsigned char c;
};

unsigned char nondet_uchar(void);
unsigned nondet_unsigned(void);

int main(void)
{
  unsigned i = nondet_unsigned();
  __CPROVER_assume(i < 2);
  union V v;
  v.c = nondet_uchar();
  union V a[2];
  a[i] = v;
  assert(a[i].c == v.c);
  return 0;
}
