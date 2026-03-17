// C++20 std::bit_cast
#include <bit>
int main()
{
  float f = 1.0f;
  unsigned int i = std::bit_cast<unsigned int>(f);
  // bit_cast type-checks and produces a value
  __CPROVER_assert(sizeof(i) == sizeof(f), "same size");
}
