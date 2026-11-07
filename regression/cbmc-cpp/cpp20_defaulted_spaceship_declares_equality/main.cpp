// N5008 [class.compare.default]/4: a class that declares no operator==
// gets one for each defaulted operator<=>, with its parameters and the
// return type bool, defined as defaulted ([class.eq]/3: memberwise ==).  A
// declared operator== (here a user-provided one in R) suppresses it.
#include <compare>
extern "C" void __CPROVER_assert(bool, const char *);
struct P
{
  int x, y;
  auto operator<=>(const P &) const = default;
};
struct F
{
  int v;
  friend auto operator<=>(const F &, const F &) = default;
};
struct R
{
  int v;
  auto operator<=>(const R &) const = default;
  bool operator==(const R &o) const
  {
    return v % 10 == o.v % 10;
  }
};
struct D : P
{
  int z;
  auto operator<=>(const D &) const = default;
};
int main()
{
  P a{1, 2}, b{1, 2}, c{1, 3};
  F f{4}, g{5};
  R r{3}, s{13};
  D d{{1, 2}, 3}, e{{1, 2}, 4};
  __CPROVER_assert(
    a == b && a != c && !(f == g) && f != g && r == s && d != e && d == d,
    "== and != from the defaulted <=>");
  __CPROVER_assert(a == c, "WRONG (must FAIL)");
  return 0;
}
