// Verify type_traits compile-time properties
#include <type_traits>

int main()
{
  static_assert(std::is_integral<int>::value, "int is integral");
  static_assert(std::is_integral<bool>::value, "bool is integral");
  static_assert(!std::is_integral<double>::value, "double is not integral");

  static_assert(std::is_same<int, int>::value, "int is same as int");
  static_assert(!std::is_same<int, double>::value, "int is not same as double");

  static_assert(std::is_pointer<int *>::value, "int* is pointer");
  static_assert(!std::is_pointer<int>::value, "int is not pointer");

  static_assert(std::is_void<void>::value, "void is void");
  static_assert(!std::is_void<int>::value, "int is not void");

  static_assert(
    std::is_floating_point<double>::value, "double is floating point");
  static_assert(
    !std::is_floating_point<int>::value, "int is not floating point");

  return 0;
}
