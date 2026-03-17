struct Point
{
  int x;
  int y;
  int z;
};

int main()
{
  Point p = {.x = 1, .y = 2, .z = 3};
  __CPROVER_assert(p.x == 1, "x");
  __CPROVER_assert(p.y == 2, "y");
  __CPROVER_assert(p.z == 3, "z");
}
