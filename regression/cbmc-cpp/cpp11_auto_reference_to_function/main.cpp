// N5008 [dcl.type.auto.deduct]/4 with [temp.deduct.call]/2-3: for `auto &f =
// twice' the declared type is a reference, so the function-to-pointer
// conversion of [temp.deduct.call]/2.2 does not apply and auto is deduced
// as the function type `int(int)'.  The front end deduced a pointer, since
// the function designator was already converted to its address, and the
// binding failed: "bad reference initializer" (CBMC's own goto-harness,
// `auto &f = harness_options_parser::require_exactly_one_value',
// dog-fooding).  [expr.unary.op]/3: `&f' is the address of the function;
// it was rejected ("address-of code requires a member expression").
extern "C" void __CPROVER_assert(bool, const char *);
int twice(int x)
{
  return 2 * x;
}
namespace ns
{
int thrice(int x)
{
  return 3 * x;
}
} // namespace ns
int main()
{
  auto &f = twice;
  const auto &g = ns::thrice;
  int (&h)(int) = twice;
  auto p = twice; // [temp.deduct.call]/2.2: a pointer
  __CPROVER_assert(f(2) == 4 && g(2) == 6 && h(1) == 2, "call through auto &");
  __CPROVER_assert(&f == &twice && p == &twice, "same function");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
