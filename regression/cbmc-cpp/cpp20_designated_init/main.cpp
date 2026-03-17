// C++20 designated initializers
struct S
{
  int x;
  int y;
};

int main()
{
  S s = {.x = 1, .y = 2};
  __CPROVER_assert(s.x == 1, "x==1");
  __CPROVER_assert(s.y == 2, "y==2");
  return 0;
}
