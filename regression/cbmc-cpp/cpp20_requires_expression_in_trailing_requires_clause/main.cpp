// N5008 [temp.pre]/1, [expr.prim.req]: a requires-clause's primary
// expression may be a requires-expression, `int f() const requires
// requires(const T &x) { x.ok(); }'.  The constraint parser did not accept
// one, so such a trailing clause was skipped (libc++'s
// view_interface::operator bool) and never checked; and a requires-
// expression with parameters, a single atomic constraint
// ([temp.constr.normal]/1.6), was split into its requirements without the
// parameters in scope.  The function's own parameters are in scope in its
// trailing requires-clause too ([basic.scope.param]/1).
extern "C" void __CPROVER_assert(bool, const char *);
struct Yes
{
  bool ok() const
  {
    return true;
  }
};
struct No
{
};
template <class T>
struct W
{
  T t;
  int how = 0;
  W()
  requires requires
  {
    T{};
  }
  = default;
  W(int)
  requires requires(const T &x)
  {
    x.ok();
  } : how(1)
  {
  }
  W(long) : how(2)
  {
  }
  int f() const requires requires(const T &x)
  {
    x.ok();
  }
  {
    return 1;
  }
  int g() const requires(sizeof(T) > 100)
  {
    return 2;
  }
  explicit operator bool() const requires requires(const T &x)
  {
    x.ok();
  }
  {
    return true;
  }
};
// [basic.scope.param]/1: the function parameters are in scope
template <class T>
int both_ok(const T &a, const T &b) requires requires
{
  a.ok() && b.ok();
}
{
  return 1;
}
inline int both_ok(...)
{
  return 2;
}

template <class X>
concept has_f = requires(X x)
{
  x.f();
};
template <class X>
concept has_g = requires(X x)
{
  x.g();
};
template <class X>
concept testable = requires(X x)
{
  static_cast<bool>(x);
};
static_assert(has_f<W<Yes>>, "f, satisfied");
static_assert(!has_f<W<No>>, "f, requires-expression unsatisfied");
static_assert(!has_g<W<Yes>>, "g, unsatisfied");
static_assert(testable<W<Yes>>, "operator bool, satisfied");
static_assert(!testable<W<No>>, "operator bool, unsatisfied");
int main()
{
  W<Yes> w{};
  __CPROVER_assert(w.f() == 1 && static_cast<bool>(w), "calls");
  __CPROVER_assert(both_ok(Yes{}, Yes{}) == 1, "parameters, satisfied");
  __CPROVER_assert(both_ok(No{}, No{}) == 2, "parameters, unsatisfied");
  W<Yes> y(1);
  W<No> n(1);
  __CPROVER_assert(y.how == 1, "constructor, satisfied");
  __CPROVER_assert(n.how == 2, "constructor, unsatisfied");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
