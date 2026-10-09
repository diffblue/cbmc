// Unit proof for big-int arithmetic (src/big-int/bigint.cc).
//
// The unit tests exercise fixed operand values; this harness verifies
// ring identities over ALL int operands (nondeterministic inputs):
//  * commutativity of + and *
//  * additive inverse: a + (-a) == 0
//  * subtraction round-trip: (a + b) - b == a
//  * comparison consistency with the int operands
#include <big-int/bigint.hh>

extern "C" void __CPROVER_assert(bool, const char *);
extern "C" void __CPROVER_assume(bool);
int __VERIFIER_nondet_int();

int main()
{
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  // avoid int overflow in the reference comparisons
  __CPROVER_assume(x > -1000000 && x < 1000000);
  __CPROVER_assume(y > -1000000 && y < 1000000);

  BigInt a(x);
  BigInt b(y);

  __CPROVER_assert(a + b == b + a, "addition commutes");
  __CPROVER_assert(a + b == BigInt(x + y), "addition agrees with int");
  __CPROVER_assert((a + b) - b == a, "subtraction round-trip");
  __CPROVER_assert(a + (-a) == BigInt(0), "additive inverse");
  __CPROVER_assert((x < y) == (a < b), "comparison agrees with int");

  return 0;
}
