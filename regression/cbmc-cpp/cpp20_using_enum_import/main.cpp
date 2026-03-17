// C++20 using enum - enumerators imported into scope
enum class Color
{
  Red,
  Green,
  Blue
};

void test()
{
  using enum Color;
  int r = (int)Red;
  __CPROVER_assert(r == 0, "using enum import");
}

int main()
{
  test();
  return 0;
}
