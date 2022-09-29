int x, y, *p;

int main()
{
  x = 10;
  p = &y;
  *p = 20;                                 // unrelated to 'x'
  __CPROVER_assert(x == 10, "property 1"); // should pass

  return 0;
}
