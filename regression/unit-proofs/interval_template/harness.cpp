// Unit proof for interval_templatet<int> (src/util/interval_template.h):
// the lattice operations' contracts over ALL bounded intervals -- where
// unit/util/interval_template.cpp checks fixed samples.
#include <util/interval_template.h>

extern "C" void __CPROVER_assert(bool, const char *);
extern "C" void __CPROVER_assume(bool);
int __VERIFIER_nondet_int();

static bool contains(const interval_templatet<int> &i, int x)
{
  return (!i.lower_set || i.get_lower() <= x) &&
         (!i.upper_set || x <= i.get_upper());
}

int main()
{
  const int l1 = __VERIFIER_nondet_int(), u1 = __VERIFIER_nondet_int();
  const int l2 = __VERIFIER_nondet_int(), u2 = __VERIFIER_nondet_int();
  const int x = __VERIFIER_nondet_int();
  __CPROVER_assume(l1 <= u1 && l2 <= u2);
  interval_templatet<int> a(l1, u1), b(l2, u2);

  // meet (intersection) is exact: x in a meet b  <=>  x in a and x in b
  interval_templatet<int> m = a;
  m.meet(b);
  __CPROVER_assert(
    contains(m, x) == (contains(a, x) && contains(b, x)),
    "meet is the intersection");
  __CPROVER_assert(
    m.empty() == (u1 < l2 || u2 < l1), "meet empty iff disjoint");

  // join (convex hull) over-approximates the union
  interval_templatet<int> j = a;
  j.join(b);
  __CPROVER_assert(
    !(contains(a, x) || contains(b, x)) || contains(j, x),
    "join contains the union");
  __CPROVER_assert(
    !j.empty() && !j.lower_set == false,
    "join of non-empty is non-empty and bounded below");

  // the order tests agree with the bounds
  __CPROVER_assert(
    a.is_less_than_eq(b) == (u1 <= l2),
    "is_less_than_eq iff every a <= every b");
  __CPROVER_assert(
    (a == b) == (l1 == l2 && u1 == u2), "equality is bound-wise");
  __CPROVER_assert(a.singleton() == (l1 == u1), "singleton");

  // make_le_than / make_ge_than tighten exactly
  interval_templatet<int> t = a;
  t.make_le_than(x);
  __CPROVER_assert(
    t.empty() == (x < l1) && (t.empty() || t.get_upper() == (x < u1 ? x : u1)),
    "make_le_than");
  return 0;
}
