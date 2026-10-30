extern "C" void __CPROVER_assert(bool, const char *);
int test(float)
{
  return 1;
}
int test(int)
{
  return 2;
}
int test(double)
{
  return 3;
}
int main()
{
  // N5008 [expr.type.conv]/2, [dcl.init.general]/9: T() value-initializes
  // a prvalue of type T, an exact match for a parameter of type T
  __CPROVER_assert(test(double()) == 3, "double() selects test(double)");
  __CPROVER_assert(test(float()) == 1, "float() selects test(float)");
  __CPROVER_assert(test(float()) == 3, "WRONG (must FAIL)");
  return 0;
}
