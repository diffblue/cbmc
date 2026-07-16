// Unit proof for tvt, CBMC's three-valued (Kleene) logic
// (src/util/threeval.h).
//
// The unit-test style would spot-check a few combinations; this harness
// proves the Kleene-logic laws over ALL pairs of truth values
// (nondeterministic inputs):
//  * De Morgan: !(a && b) == (!a || !b), !(a || b) == (!a && !b)
//  * double negation, commutativity, idempotence
//  * is_known/is_unknown consistency
#include <util/threeval.h>

extern "C" void __CPROVER_assert(bool, const char *);
extern "C" void __CPROVER_assume(bool);
int __VERIFIER_nondet_int();

static tvt nondet_tvt()
{
  int v = __VERIFIER_nondet_int();
  __CPROVER_assume(v >= 0 && v <= 2);
  if(v == 0)
    return tvt(tvt::tv_enumt::TV_FALSE);
  if(v == 1)
    return tvt(tvt::tv_enumt::TV_UNKNOWN);
  return tvt(tvt::tv_enumt::TV_TRUE);
}

int main()
{
  tvt a = nondet_tvt();
  tvt b = nondet_tvt();

  // De Morgan ([Kleene K3] laws)
  __CPROVER_assert((!(a && b)) == (!a || !b), "De Morgan and");
  __CPROVER_assert((!(a || b)) == (!a && !b), "De Morgan or");

  // double negation
  __CPROVER_assert(!!a == a, "double negation");

  // commutativity
  __CPROVER_assert((a && b) == (b && a), "and commutes");
  __CPROVER_assert((a || b) == (b || a), "or commutes");

  // idempotence
  __CPROVER_assert((a && a) == a, "and idempotent");
  __CPROVER_assert((a || a) == a, "or idempotent");

  // known/unknown consistency
  __CPROVER_assert(a.is_known() == !a.is_unknown(), "known vs unknown");
  __CPROVER_assert(
    a.is_known() == (a.is_true() || a.is_false()), "known is true-or-false");

  return 0;
}
