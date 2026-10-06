// N5008 [expr.new]/24, [dcl.init.general]/16.5: `new T[n](e1, ..., ek)'
// initializes the first k elements from the expression-list and
// value-initializes the rest
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  int *a = new int[3](1, 2);
  __CPROVER_assert(a[0] == 1 && a[1] == 2 && a[2] == 0, "parenthesized");
  __CPROVER_assert(a[2] == 1, "WRONG (must FAIL)");
}
