// C++20 aggregate initialization with parentheses
struct S
{
  int x;
  int y;
};

int main()
{
  S s(1, 2);
  __CPROVER_assert(s.x == 1 && s.y == 2, "aggregate paren init");
  return 0;
}
