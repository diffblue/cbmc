int x, y, *p;

int main()
{
  x = 10;
  p = &x;
  y = *p;
  __CPROVER_assert(y == 10, "property 1"); // should pass

  return 0;
}
