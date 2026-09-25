// C++20 three-way comparison with strong_ordering
namespace std
{
struct strong_ordering
{
  int _v;
  constexpr explicit strong_ordering(int v) : _v(v)
  {
  }
  static const strong_ordering less;
  static const strong_ordering equal;
  static const strong_ordering greater;
  constexpr bool operator==(strong_ordering o) const
  {
    return _v == o._v;
  }
};
constexpr strong_ordering strong_ordering::less(-1);
constexpr strong_ordering strong_ordering::equal(0);
constexpr strong_ordering strong_ordering::greater(1);
} // namespace std
struct S
{
  int x;
  std::strong_ordering operator<=>(const S &o) const
  {
    if(x < o.x)
      return std::strong_ordering::less;
    if(x > o.x)
      return std::strong_ordering::greater;
    return std::strong_ordering::equal;
  }
};
int main()
{
  S a{1}, b{2};
  // clang-format off
  auto r = a <=> b;
  // clang-format on
  __CPROVER_assert(r == std::strong_ordering::less, "1 <=> 2 is less");
  return 0;
}
