// C++11 scoped enum
enum class Color : int
{
  Red = 1,
  Green = 2,
  Blue = 3
};
int main()
{
  Color c = Color::Green;
  __CPROVER_assert(static_cast<int>(c) == 2, "scoped enum");
  return 0;
}
