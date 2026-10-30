extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  int b = 1;
  int &x = b;
  // [expr.pre.incr]/1, [expr.assign]/1: both results are lvalues referring
  // to the operand
  ++(++x);
  __CPROVER_assert(b == 3, "prefix increment of prefix increment");
  (x = 5) = 7;
  __CPROVER_assert(b == 7, "assignment to assignment");
  int *p = &b;
  (*p *= 2) -= 1;
  __CPROVER_assert(b == 13, "through a pointer");
  __CPROVER_assert(b != 13, "WRONG (must FAIL)");
}
