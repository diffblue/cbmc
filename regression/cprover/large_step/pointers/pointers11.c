int main()
{
  int *p;
  *p = 123;
  __CPROVER_assert(*p == 123, "property 1"); // should pass
  return 0;
}
