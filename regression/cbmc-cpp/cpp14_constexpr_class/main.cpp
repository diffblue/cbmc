struct Point
{
  int x, y;
  constexpr Point(int a, int b) : x(a), y(b)
  {
  }
  constexpr int sum() const
  {
    return x + y;
  }
};

int main()
{
  constexpr Point p(3, 4);
  __CPROVER_assert(p.sum() == 7, "constexpr class");
  return 0;
}
