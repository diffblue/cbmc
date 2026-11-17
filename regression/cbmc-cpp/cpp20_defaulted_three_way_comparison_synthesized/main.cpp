// N5008 [class.spaceship]/1.3-1.6, /2.2: a defaulted operator<=> with a
// declared comparison category R compares a member without a usable <=>
// through its == and <: the synthesized three-way comparison of type R.
// An operand of reference type of the built-in <=> denotes the referenced
// object ([expr.type]/1).
#include <compare>
extern "C" void __CPROVER_assert(bool, const char *);
struct M
{
  int v;
  bool operator==(const M &o) const
  {
    return v == o.v;
  }
  bool operator<(const M &o) const
  {
    return v < o.v;
  }
};
struct S
{
  M m;
  std::strong_ordering operator<=>(const S &) const = default;
};
struct W
{
  M m;
  std::weak_ordering operator<=>(const W &) const = default;
};
struct P
{
  M m;
  std::partial_ordering operator<=>(const P &) const = default;
};
int main()
{
  S s1{{1}}, s2{{2}};
  __CPROVER_assert(s1 < s2 && !(s2 < s1), "strong_ordering");
  __CPROVER_assert((s1 <=> s1) == 0, "strong_ordering, equal");
  W w1{{3}}, w2{{2}};
  __CPROVER_assert(w1 > w2, "weak_ordering");
  P p1{{1}}, p2{{1}};
  __CPROVER_assert(p1 <= p2 && p1 >= p2, "partial_ordering");
  int i = 1, j = 2;
  int &ri = i, &rj = j;
  __CPROVER_assert((ri <=> rj) < 0, "reference operands");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
