// C++17 std::any
#include <any>
int main()
{
  // std::any constructor template fails on GCC 12 (deferred type-checking)
  // and GCC 15+ (noexcept specifier with __is_nothrow_new_constructible).
  // Works on GCC 13-14 and Clang.
#if !defined(__GNUC__) || defined(__clang__) ||                                \
  (__GNUC__ >= 13 && __GNUC__ <= 14)
  std::any a = 42;
  __CPROVER_assert(std::any_cast<int>(a) == 42, "any value");
#endif
}
