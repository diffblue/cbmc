extern "C" void __CPROVER_assert(bool, const char *);
int h(float)
{
  return 1;
}
int h(double)
{
  return 2;
}
template <class V>
int fmt(V v)
{
  return h(v);
}
template <class Fn>
int visit(Fn f)
{
  double d = 1.0;
  return f(d);
}
int main()
{
  // [expr.prim.lambda.closure]/4: the function call operator of a generic
  // lambda is a template; its body is instantiated for auto = double only
  int r = visit([](auto &a) { return fmt(a); });
  __CPROVER_assert(r == 2, "generic lambda");
  __CPROVER_assert(r != 2, "WRONG (must FAIL)");
}
