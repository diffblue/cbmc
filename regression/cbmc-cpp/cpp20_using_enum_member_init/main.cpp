// C++20 using enum in class with default member initializer
enum class Color
{
  Red,
  Green,
  Blue
};

struct S
{
  using enum Color;
  Color c = Red;
};

int main()
{
  S s;
  __CPROVER_assert(s.c == Color::Red, "using enum in class");
}
