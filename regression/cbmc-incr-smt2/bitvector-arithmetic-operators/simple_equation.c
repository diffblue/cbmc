#include <stdlib.h>

int main()
{
  int a;
  __CPROVER_assume(a < 100);
  __CPROVER_assume(a > -100);
  __CPROVER_assume(a != 0);

  // Simple algebraic identities - expected to drive the SMT backend
  __CPROVER_assert(a + a == a * 2, "a plus a always equals two times a");
  __CPROVER_assert(a - a == 0, "a minus a always equals 0");
  __CPROVER_assert(a + -a == 0, "a plus its additive inverse equals 0");
  __CPROVER_assert(
    a - -a == 2 * a, "a minus its additive inverse equals two times a");
  __CPROVER_assert((a * a) / a == a, "a squared divided by a equals a");
  __CPROVER_assert((2 * a) / a == 2, "two times a divided by a equals two");
  __CPROVER_assert(a % a == 0, "a mod itself equals 0");

  // Same round of tests, but for a type of different size
  long long int b;
  __CPROVER_assume(b < 100ll);
  __CPROVER_assume(b > -100ll);
  __CPROVER_assume(b != 0ll);

  __CPROVER_assert(b + b == b * 2ll, "b plus b always equals two times b");
  __CPROVER_assert(b - b == 0ll, "b minus b always equals 0");
  __CPROVER_assert(b + -b == 0ll, "b plus its additive inverse equals 0");
  __CPROVER_assert(
    b - -b == 2ll * b, "b minus its additive inverse equals two times b");
  __CPROVER_assert((b * b) / b == b, "b squared divided by b equals b");
  __CPROVER_assert((2ll * b) / b == 2ll, "two times b divided by b equals two");
  __CPROVER_assert(b % b == 0ll, "b mod itself equals 0");
}
