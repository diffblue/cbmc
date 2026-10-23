// N5008 [expr.prim.lambda.capture]/8, [class.mfct.non.static]/2: in the
// body of a lambda that captures `this' (here by the capture-default [&]),
// the qualified call `base::value(x)' is `(*this).base::value(x)' on the
// enclosing object -- a non-virtual call of base's function.  Only
// unqualified member calls were routed through the captured `this'; the
// qualified one used the closure object: "invalid implicit conversion from
// '...__lambda_0_closure' to 'const struct base &'" (CBMC's own
// havoc_if_validt in contracts/utils.cpp, dog-fooding).
extern "C" void __CPROVER_assert(bool, const char *);
struct base
{
  int k = 3;
  virtual ~base() = default;
  virtual int value(int x) const
  {
    return k + x;
  }
};
template <class F>
int call(F f)
{
  return f();
}
struct derived : base
{
  int value(int x) const override
  {
    // N5008 [expr.prim.lambda.capture]/7, [class.mfct.non.static]/2: in the
    // lambda body `base::value(x)' is (*this).base::value(x) for the
    // captured this, a non-virtual call of base's function
    return call([&]() { return base::value(x) * 10; });
  }
};
int main()
{
  derived d;
  __CPROVER_assert(d.value(1) == 40, "qualified base call in a lambda");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
