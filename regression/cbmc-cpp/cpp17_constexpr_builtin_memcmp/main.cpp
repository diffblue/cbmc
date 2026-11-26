// GCC and clang evaluate __builtin_memcmp in a constant expression
// (an extension: N5008 [expr.const]/10.3 excludes non-constexpr functions);
// libstdc++ 11's char_traits<char>::compare, used by string_view's
// comparisons and ends_with, calls it.  Bytes compare as unsigned char.
#include <string_view>

constexpr int sign(int r)
{
  return r < 0 ? -1 : r > 0 ? 1 : 0;
}

constexpr bool view_ends_with(std::string_view s, std::string_view suffix)
{
  return s.size() >= suffix.size() &&
         __builtin_memcmp(
           s.data() + s.size() - suffix.size(), suffix.data(), suffix.size()) ==
           0;
}

constexpr char bytes[] = {'a', '\xff', 'c'};
constexpr char other[] = {'a', '\x01', 'c'};

int main()
{
  static_assert(__builtin_memcmp("abc", "abc", 3) == 0, "");
  static_assert(sign(__builtin_memcmp("abc", "abd", 3)) == -1, "");
  static_assert(sign(__builtin_memcmp("abd", "abc", 3)) == 1, "");
  static_assert(__builtin_memcmp("abc", "abd", 2) == 0, "");
  static_assert(__builtin_memcmp("abc", "xyz", 0) == 0, "");
  // '\xff' is 255 as unsigned char, greater than 1
  static_assert(sign(__builtin_memcmp(bytes, other, 3)) == 1, "");
  static_assert(view_ends_with("UTF-32LE", "LE"), "");
  static_assert(!view_ends_with("UTF-32LE", "BE"), "");
  static_assert(std::string_view{"32"} == "32", "");
  static_assert(std::string_view{"32"} != "33", "");
  int n = 3;
  __CPROVER_assert(__builtin_memcmp("abc", "abd", n) != 0, "run time");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
