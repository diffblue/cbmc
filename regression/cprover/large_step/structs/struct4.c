struct S
{
  int x, y;
} a = {.x = 10, .y = 20};

int main()
{
  __CPROVER_assert(a.x == 10, "property 1"); // should pass
  __CPROVER_assert(a.y == 20, "property 2"); // should pass
  return 0;
}
