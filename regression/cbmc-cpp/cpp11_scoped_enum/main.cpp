// C++11 scoped enum
enum class Color
{
  Red,
  Green,
  Blue
};
int main()
{
  Color c = Color::Green;
  __CPROVER_assert(static_cast<int>(c) == 1, "scoped enum");
  return 0;
}
