#include <assert.h>

enum E
{
  A = 1,
  B = 3
};

enum E nondet_enum(void);
double nondet_double(void);

int main(void)
{
  enum E e = nondet_enum();
  __CPROVER_assume(e == B);
  double d = e;
  assert(d == 3.0);

  double x = nondet_double();
  __CPROVER_assume(x == 3.0);
  enum E f = (enum E)x;
  assert(f == B);
  return 0;
}
