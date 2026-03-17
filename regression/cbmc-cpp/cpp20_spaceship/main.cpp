// C++20 three-way comparison (spaceship operator)
struct S
{
  int x;
  // clang-format off
  friend int operator<=>(const S &a, const S &b)
  {
    return a.x - b.x;
  }
  // clang-format on
};

int main()
{
  S a{1}, b{2};
  // clang-format off
  __CPROVER_assert((a <=> b) < 0, "1 < 2");
  // clang-format on
  return 0;
}
