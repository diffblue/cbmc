// C++11 delegating constructor
struct S
{
  int x, y;
  S(int a, int b) : x(a), y(b)
  {
  }
  S(int a) : S(a, a * 2)
  {
  }
};
int main()
{
  S s(5);
  __CPROVER_assert(s.x == 5, "delegating x");
  __CPROVER_assert(s.y == 10, "delegating y");
  return 0;
}
