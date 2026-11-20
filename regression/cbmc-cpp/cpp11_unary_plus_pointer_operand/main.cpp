// N5008 [expr.unary.op]/7: the operand of the unary + operator shall be a
// prvalue of arithmetic, unscoped enumeration, or pointer type.  After the
// array-to-pointer or function-to-pointer conversion, `+"__"', `+a' and
// `+f' are pointers.  The front end used C's rule (arithmetic operands
// only): "operator 'unary+' not defined for type 'const char *'" (CBMC's own
// contracts.cpp and dfcc_instrument_loop.cpp, `s + +"__"', dog-fooding).
extern "C" void __CPROVER_assert(bool, const char *);
int f(int x)
{
  return x + 1;
}
int main()
{
  const char *s = +"__";
  int a[3] = {1, 2, 3};
  int *p = +a;
  int (*fp)(int) = +f;
  char c = 'A';
  // [expr.unary.op]/7: an integral operand is promoted
  __CPROVER_assert(sizeof(+c) == sizeof(int), "promotion");
  __CPROVER_assert(s[0] == '_' && s[2] == 0, "string literal decays");
  __CPROVER_assert(p == &a[0] && +p == p, "array decays");
  __CPROVER_assert(fp(1) == 2, "function decays");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
