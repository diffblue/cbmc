struct S
{
  int x, y;
} a, b;

int main()
{
  a.x = 1;
  b = a;                                      // copy entire struct
  __CPROVER_assert(a.x == 1, "property 1");   // should pass
  __CPROVER_assert(b.x == 1, "property 2");   // should pass
  __CPROVER_assert(b.y == a.y, "property 3"); // should pass
  return 0;
}
