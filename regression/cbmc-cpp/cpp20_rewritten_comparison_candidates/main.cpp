// clang-format off
#include <compare>
extern "C" void __CPROVER_assert(bool, const char *);
struct P
{
  int a;
  friend constexpr std::strong_ordering operator<=>(const P &x, const P &y)
  {
    return x.a <=> y.a;
  }
  friend constexpr bool operator==(const P &x, const P &y)
  {
    return x.a == y.a;
  }
};
static_assert(std::three_way_comparable_with<P, P>);
static_assert(std::three_way_comparable<P>);
int main()
{
  P p{1}, q{2};
  __CPROVER_assert(p < q, "rewritten < from <=>");
  __CPROVER_assert(
    q > p && p <= q && q >= p && p != q, "other rewritten comparisons");
  __CPROVER_assert(
    noexcept(p < q) == false, "noexcept of rewritten (not noexcept here)");
  __CPROVER_assert(q < p, "WRONG (must FAIL)");
}
// clang-format on
