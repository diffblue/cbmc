// clang-format off
#include <compare>
#include <memory>
extern "C" void __CPROVER_assert(bool, const char *);
class category
{
public:
  bool operator==(const category &rhs) const noexcept
  {
    return this == &rhs;
  }
  std::strong_ordering operator<=>(const category &rhs) const noexcept
  {
    return std::compare_three_way()(this, std::addressof(rhs));
  }
};
int main()
{
  category a, b;
  __CPROVER_assert(a == a && !(a == b), "identity comparison");
  __CPROVER_assert((a <=> a) == 0, "compare_three_way on pointers: equal");
  __CPROVER_assert((a <=> b) != 0, "compare_three_way on pointers: distinct");
  __CPROVER_assert((a <=> a) != 0, "WRONG (must FAIL)");
}
// clang-format on
