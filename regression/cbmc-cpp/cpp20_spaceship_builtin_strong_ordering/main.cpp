// N5008 [expr.spaceship]/8: the built-in three-way comparison of two operands
// of integral type yields a value of type std::strong_ordering (equal / less /
// greater), NOT an int.  Header-free model of <compare>'s strong_ordering
// (whose only public constructor is explicit, exactly like the real type, so
// an int result could not implicitly convert to it).  Well-defined under a
// conforming compiler.
//
// KNOWNBUG: CBMC lowered a built-in `a <=> b` to a plain int, so binding it to
// a std::strong_ordering reported "invalid implicit conversion from signed int
// to strong_ordering" (CONVERSION ERROR).
namespace std
{
struct strong_ordering
{
  int _v;
  constexpr explicit strong_ordering(int v) : _v(v) {}
  static const strong_ordering less;
  static const strong_ordering equal;
  static const strong_ordering greater;
  constexpr bool operator==(strong_ordering o) const { return _v == o._v; }
};
constexpr strong_ordering strong_ordering::less{-1};
constexpr strong_ordering strong_ordering::equal{0};
constexpr strong_ordering strong_ordering::greater{1};
} // namespace std

int main()
{
  int a = 1, b = 2;
  std::strong_ordering r = a <=> b;
  __CPROVER_assert(r == std::strong_ordering::less, "1 <=> 2 is less");
  __CPROVER_assert((5 <=> 5) == std::strong_ordering::equal, "5 <=> 5 is equal");
  __CPROVER_assert((9 <=> 4) == std::strong_ordering::greater, "9 <=> 4 greater");
  return 0;
}
