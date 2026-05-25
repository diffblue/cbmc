#include <type_traits>

static_assert(std::is_trivially_constructible<int>::value, "");
// is_trivially_copy/move_constructible requires __is_constructible(T, const T&)
// which works on GCC 13+ but the template chain fails on GCC 11/12.
#if !defined(__GNUC__) && !defined(_MSC_VER) || defined(__clang__) ||          \
  __GNUC__ >= 13
static_assert(std::is_trivially_copy_constructible<int>::value, "");
static_assert(std::is_trivially_move_constructible<int>::value, "");
#endif
static_assert(std::is_nothrow_constructible<int>::value, "");

int main()
{
  return 0;
}
