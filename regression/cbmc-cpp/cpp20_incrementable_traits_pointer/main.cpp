// libstdc++'s <iterator> under -std=c++20: incrementable_traits<int *> --
// its partial specializations `requires is_object_v<_Tp>' for `_Tp *' and
// `requires requires { typename _Iter::difference_type; }' for `_Iter'.
// Checking the second for `int *' resolved `int *::difference_type'
// (ill-formed, N5008 [basic.lookup.qual.general]/1 -- a substitution
// failure here) by a name-based scope search that found the class being
// matched and re-elaborated it without end (stack overflow).  A
// specialization whose partial specializations are being matched is not
// elaborated again from within that matching.
#include <array>
#include <iterator>
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  std::array<int, 3> a = {1, 2, 3};
  __CPROVER_assert(a[1] == 2, "array element");
  int raw[3] = {4, 5, 6};
  __CPROVER_assert(std::distance(raw, raw + 3) == 3, "distance over pointers");
  static_assert(
    std::same_as<
      std::incrementable_traits<int *>::difference_type,
      std::ptrdiff_t>,
    "pointer difference_type");
  return 0;
}
