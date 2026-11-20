extern "C" void __CPROVER_assert(bool, const char *);
int &add(int &x, int a, int c)
{
  return (x += a) += c; // [expr.assign]/1
}
int main()
{
  int b = 1;
  __CPROVER_assert(&add(b, 2, 3) == &b, "refers to the left operand");
  __CPROVER_assert(b == 6, "both assignments");
  __CPROVER_assert(b == 7, "WRONG (must FAIL)");
}
