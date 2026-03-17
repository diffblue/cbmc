// C++11 return with braces
struct Point
{
  int x;
  int y;
};
Point make_point()
{
  return {3, 4};
}
int main()
{
  Point p = make_point();
  __CPROVER_assert(p.x == 3, "return braces x");
  __CPROVER_assert(p.y == 4, "return braces y");
  return 0;
}
