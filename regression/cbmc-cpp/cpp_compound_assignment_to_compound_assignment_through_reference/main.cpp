extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  int b = 1;
  int &x = b;
  // [expr.assign]/1: the result of a compound assignment is an lvalue
  // referring to its left operand, here the object x refers to
  (x += 2) += 3;
  __CPROVER_assert(b == 6, "both assignments");
  __CPROVER_assert(b == 7, "WRONG (must FAIL)");
}
