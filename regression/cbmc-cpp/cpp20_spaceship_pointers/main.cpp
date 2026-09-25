// N5008 [expr.spaceship]/8: for two operands of pointer type (after the
// composite pointer type conversion) `p <=> q' yields std::strong_ordering
// (less, equal, greater by the pointer comparison).  Only arithmetic operands
// were lowered to the comparison-category constants; pointer operands fell to
// the C front end's int lowering, so a function returning strong_ordering
// from `if(const auto cmp = x.p <=> y.p; cmp != 0) return cmp;' failed
// ("found no match for symbol 'strong_ordering'") -- libstdc++ 16's
// _Bit_iterator_base::operator<=>, behind every std::vector<bool> use and
// the gcc16 vector_find KNOWNBUG.  Found by the cvise reduction of that test.
// clang-format off
#include <compare>
extern "C" void __CPROVER_assert(bool, const char *);
struct It
{
  unsigned long *p;
  friend constexpr std::strong_ordering operator<=>(const It &x, const It &y) noexcept
  {
    if(const auto cmp = x.p <=> y.p; cmp != 0)
      return cmp;
    return std::strong_ordering::equal;
  }
};
int main()
{
  unsigned long a[2];
  It x{a}, y{a + 1};
  __CPROVER_assert((x <=> y) < 0, "less");
  __CPROVER_assert((x <=> x) == 0, "equal");
  __CPROVER_assert((y <=> x) > 0, "greater");
  __CPROVER_assert((x <=> y) > 0, "WRONG (must FAIL)");
}
