#include <limits.h>

enum E
{
  V1 = 1,
  V2 = 2
};

struct B
{
  unsigned b : 2;
};

int main()
{
  unsigned __int128 int x = __VERIFIER_nondet_int();
  __CPROVER_assume(x < (~(unsigned __int128)0) - 4);

  enum E e = __VERIFIER_nondet_int();
  __CPROVER_assume(__CPROVER_enum_is_in_range(e));
  __CPROVER_assert(x + e > x, "long long plus enum");

  struct B nondet_B(void);
  struct B b = nondet_B();
  __CPROVER_assert(x + b.b >= x, "long long plus bitfield");
}
