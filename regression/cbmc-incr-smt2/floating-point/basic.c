int main()
{
  float x = 1.0f;
  float y = 2.0f;
  __CPROVER_assert(x + y == 3.0f, "float add");
  __CPROVER_assert(x < y, "float lt");
  __CPROVER_assert(x != y, "float ne");
  __CPROVER_assert(!(x != x), "x == x");
}
