// C++20 using enum
enum class Color
{
  Red,
  Green,
  Blue
};

void use_enum()
{
  using enum Color;
  // After using enum, enumerators are in scope
}

int main()
{
  Color c = Color::Red;
  __CPROVER_assert((int)c == 0, "Red==0");
  return 0;
}
