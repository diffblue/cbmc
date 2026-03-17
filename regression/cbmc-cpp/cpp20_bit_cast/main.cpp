// C++20 std::bit_cast
#include <bit>
int main()
{
  float f = 1.0f;
  unsigned int i = std::bit_cast<unsigned int>(f);
  __CPROVER_assert(i == 0x3f800000u, "bit_cast");
}
