int x, *p;

int main()
{
  x = 10;
  p = &x;
  *p = 20;
  __CPROVER_assert(x == 20, "property 1"); // passes
  __CPROVER_assert(x == 10, "property 2"); // fails

  return 0;
}
