#include <type_traits>

static_assert(std::is_trivially_constructible<int>::value, "");
static_assert(std::is_trivially_copy_constructible<int>::value, "");
static_assert(std::is_trivially_move_constructible<int>::value, "");
static_assert(std::is_nothrow_constructible<int>::value, "");

int main()
{
  return 0;
}
