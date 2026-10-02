extern "C" void __CPROVER_assert(bool, const char *);
// [expr.prim.lambda.closure]/4: a generic lambda passed to a function
// template is called with a double, so its operator() is instantiated for
// double, not int
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
struct S
{
  int k = 10;
  int run()
  {
    return visit([this](auto &a) { return fmt(a) + k; });
  }
};
int main()
{
  S s;
  __CPROVER_assert(s.run() == 12, "generic lambda capturing this");
  __CPROVER_assert(s.run() != 12, "WRONG (must FAIL)");
}
