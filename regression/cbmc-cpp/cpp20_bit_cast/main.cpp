#include <version>
#if defined(__cpp_lib_bit_cast) || (__has_include(<bit>) && (!defined(__GNUC__) || __GNUC__ >= 11))
// C++20 std::bit_cast
#  include <bit>
int main()
{
  float f = 1.0f;
  unsigned int i = std::bit_cast<unsigned int>(f);
  __CPROVER_assert(i == 0x3f800000u, "IEEE 754 bit pattern");
}
#else
int main()
{
}
#endif
