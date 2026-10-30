// C++23 std::optional monadic operations
// Requires GCC 12+ or Clang (libstdc++ 11 has no optional::transform).
#if !defined(__GNUC__) && !defined(_MSC_VER) || defined(__clang__) ||          \
  __GNUC__ >= 12
#  include <optional>
int main()
{
  std::optional<int> o = 42;
  auto r = o.transform([](int x) { return x * 2; });
  __CPROVER_assert(r.has_value(), "has value");
  __CPROVER_assert(*r == 84, "transformed");
}
#else
int main()
{
}
#endif
