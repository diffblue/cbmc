// C++20 using enum
enum class Color
{
  Red,
  Green,
  Blue
};
int main()
{
  using enum Color;
  Color c = Green;
  __CPROVER_assert(static_cast<int>(c) == 1, "using enum");
  return 0;
}
