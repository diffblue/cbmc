// N5008 [expr.prim.this]/2, [class.mfct.non.static]/2: in a lambda that
// captures `this', `this' and unqualified member function calls refer to
// the enclosing object
extern "C" void __CPROVER_assert(bool, const char *);
template <class F>
int call_with(F f, int x)
{
  return f(x);
}
struct A
{
  int v;
};
// libstdc++ <format>'s visit_format_arg: a visitor called with several types
template <class F>
int visit_both(F f)
{
  return f(4) + f(A{6});
}
class S
{
  int base = 10;
  int twice(int x) const
  {
    return 2 * x;
  }
  template <class T>
  int get(const T &) const
  {
    return sizeof(T) == sizeof(int) ? 1 : 0;
  }
  static int value(int x)
  {
    return x;
  }
  static int value(const A &a)
  {
    return a.v + 100;
  }

public:
  int explicit_this()
  {
    return call_with([this](int x) { return this->base + x; }, 1);
  }
  int member_call()
  {
    return call_with([this](int x) { return twice(x) + base; }, 3);
  }
  int generic()
  {
    // a generic lambda called with a class type: the call operator is a
    // template ([expr.prim.lambda.closure]/7)
    return visit_both([this](const auto &x)
                      { return this->twice(value(x)) + get(x); });
  }
  int by_default()
  {
    int k = 7;
    return call_with([&](int x) { return twice(x) + k + this->base; }, 1);
  }
  int modifies()
  {
    call_with(
      [this](int x)
      {
        this->base += x;
        return 0;
      },
      5);
    return base;
  }
};
int main()
{
  S s;
  __CPROVER_assert(s.explicit_this() == 11, "explicit this");
  __CPROVER_assert(s.member_call() == 16, "member function call");
  __CPROVER_assert(s.generic() == 222, "generic lambda");
  __CPROVER_assert(s.by_default() == 19, "capture-default");
  __CPROVER_assert(s.modifies() == 15, "modifies the object");
  __CPROVER_assert(s.modifies() != 20, "WRONG (must FAIL)");
}
