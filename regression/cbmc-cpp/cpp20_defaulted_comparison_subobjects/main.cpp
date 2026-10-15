// clang-format off
// N5008 [class.spaceship]/2-4, [class.eq]/2-3, [class.compare.default]/6:
// defaulted comparisons compare the expanded list of subobjects -- bases,
// members, array elements -- and an `auto' operator<=> returns the common
// comparison type
#include <compare>
extern "C" void __CPROVER_assert(bool, const char *);
struct W
{
  int i;
  double d;
  auto operator<=>(const W &) const = default;
};
struct B
{
  int b;
  auto operator<=>(const B &) const = default;
  bool operator==(const B &) const = default;
};
struct D : B
{
  int arr[2];
  auto operator<=>(const D &) const = default;
  bool operator==(const D &) const = default;
};
struct N
{
  int i;
  std::weak_ordering operator<=>(const N &) const = default;
};
int main()
{
  W w1{1, 2.0}, w2{1, 3.0};
  __CPROVER_assert(
    __is_same(decltype(w1 <=> w2), std::partial_ordering) && w1 < w2,
    "common comparison type");
  D x{{1}, {1, 2}}, y{{1}, {1, 3}}, z{{2}, {0, 0}};
  __CPROVER_assert(x < y && x < z && !(z < x), "base, then array elements");
  __CPROVER_assert(x == x && !(x == y) && !(x == z), "defaulted ==");
  N n{1}, o{2};
  __CPROVER_assert(
    __is_same(decltype(n <=> o), std::weak_ordering) && n < o,
    "declared return type");
  __CPROVER_assert(x == y, "WRONG (must FAIL)");
}
// clang-format on
