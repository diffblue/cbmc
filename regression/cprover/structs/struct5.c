struct S
{
  int x, y;
} a, b;

int main()
{
  a.x = 1;
  a.y = 2;
  b.x = 1;
  b.y = 2;
  __CPROVER_assert(a == b, "property 1"); // should pass
  return 0;
}
