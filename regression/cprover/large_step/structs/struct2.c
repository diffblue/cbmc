struct S
{
  int x, y;
} s;

int main()
{
  s.x = 1;
  s.y = 2;
  __CPROVER_assert(s.x == 1, "property 1");
  __CPROVER_assert(s.y == 2, "property 2");
}
