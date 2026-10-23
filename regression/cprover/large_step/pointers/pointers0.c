int main()
{
  int x, *p;
  p = &x;
  __CPROVER_assert(*p == x, "property 1"); // should pass
  return 0;
}
