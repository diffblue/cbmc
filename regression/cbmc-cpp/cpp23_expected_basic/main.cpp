// Requires GCC 12+ or Clang (older libstdc++ lacks support).
#if !defined(__GNUC__) && !defined(_MSC_VER) || defined(__clang__) || __GNUC__ >= 12
// C++23 std::expected basic usage
#  include <expected>

int main()
{
  std::expected<int, int> e(42);
  __CPROVER_assert(e.has_value(), "has value");
  __CPROVER_assert(*e == 42, "value");
  return 0;
}
#else
int main()
{
}
#endif
