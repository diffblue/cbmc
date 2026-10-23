#include <cassert>
enum class Color : int;
enum class Color : int
{
  Red,
  Green,
  Blue
};
int main()
{
  Color c = Color::Green;
  assert(static_cast<int>(c) == 1);
  return 0;
}
