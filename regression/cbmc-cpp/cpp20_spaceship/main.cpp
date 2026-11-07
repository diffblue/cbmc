// C++20 three-way comparison (spaceship operator)
struct S
{
  int x;
  friend int operator<=>(const S &a, const S &b)
  {
    return a.x - b.x;
  }
};

int main()
{
  S a{1}, b{2};
  __CPROVER_assert((a <=> b) < 0, "1 < 2");
  return 0;
}
