extern "C" void __CPROVER_assert(bool, const char *);
// Header-free model of <compare>'s strong_ordering
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
constexpr strong_ordering strong_ordering::less{-1};
constexpr strong_ordering strong_ordering::equal{0};
constexpr strong_ordering strong_ordering::greater{1};
} // namespace std
template <class T, class U>
struct is_same
{
  static constexpr bool value = false;
};
template <class T>
struct is_same<T, T>
{
  static constexpr bool value = true;
};
struct object
{
  int v;
};
int main()
{
  object a, b;
  object *p = &a, *q = &b;
  // clang-format off
  // (clang-format 15 with the repository's c++17 setting splits `<=>')
  // [expr.spaceship]/2, /6: a prvalue of type std::strong_ordering, not of
  // the (const) type of the static member it yields
  static_assert(
    is_same<decltype(p <=> q), std::strong_ordering>::value,
    "the type is std::strong_ordering, not const std::strong_ordering");
  __CPROVER_assert((p <=> p) == std::strong_ordering::equal, "equal pointers");
  // pointers to different objects compare unequal: less or greater, the
  // order being unspecified ([expr.rel]/4), but never equal
  __CPROVER_assert(!((p <=> q) == std::strong_ordering::equal), "distinct objects");
  object arr[2];
  __CPROVER_assert((&arr[0] <=> &arr[1]) == std::strong_ordering::less, "array elements are ordered");
  __CPROVER_assert((p <=> q) == std::strong_ordering::equal, "WRONG (must FAIL)");
  // clang-format on
}
