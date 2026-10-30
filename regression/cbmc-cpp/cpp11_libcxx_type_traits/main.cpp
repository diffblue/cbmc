// libc++ type_traits — test traits that don't use compiler builtins
#include <type_traits>
static_assert(std::is_same<int, int>::value, "same");
static_assert(!std::is_same<int, double>::value, "not same");
static_assert(std::is_const<const int>::value, "const");
static_assert(!std::is_const<int>::value, "not const");
static_assert(std::is_pointer<int *>::value, "pointer");
int main()
{
}
