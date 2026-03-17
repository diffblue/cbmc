// C++23 std::to_underlying
#include <utility>
enum class Color : int
{
  Red = 1,
  Green = 2,
  Blue = 3
};
int main()
{
  __CPROVER_assert(std::to_underlying(Color::Red) == 1, "to_underlying");
}
