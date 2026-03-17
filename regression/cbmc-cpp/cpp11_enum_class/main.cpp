#include <cassert>

enum class Color : int
{
  Red = 0,
  Green = 1,
  Blue = 2
};

int main()
{
  Color c = Color::Green;
  assert(c == Color::Green);
  assert(static_cast<int>(c) == 1);
  return 0;
}
